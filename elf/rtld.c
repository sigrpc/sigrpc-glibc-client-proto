/* Run time dynamic linker.
   Copyright (C) 1995-2022 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <https://www.gnu.org/licenses/>.  */

/* Modified by Keita HAGIWARA, 2025.
   - Add prototype implementation for SigRPC functionality.  */

#include <errno.h>
#include <dlfcn.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <ldsodefs.h>
#include <_itoa.h>
#include <entry.h>
#include <fpu_control.h>
#include <hp-timing.h>
#include <libc-lock.h>
#include <unsecvars.h>
#include <dl-cache.h>
#include <dl-osinfo.h>
#include <dl-procinfo.h>
#include <dl-prop.h>
#include <dl-vdso.h>
#include <dl-vdso-setup.h>
#include <tls.h>
#include <stap-probe.h>
#include <stackinfo.h>
#include <not-cancel.h>
#include <array_length.h>
#include <libc-early-init.h>
#include <dl-main.h>
#include <gnu/lib-names.h>
#include <dl-tunables.h>
#include <get-dynamic-info.h>
#include <dl-execve.h>
#include <dl-find_object.h>
#include <dl-audit-check.h>

#include <assert.h>

/* This #define produces dynamic linking inline functions for
   bootstrap relocation instead of general-purpose relocation.
   Since ld.so must not have any undefined symbols the result
   is trivial: always the map of ld.so itself.  */
#define RTLD_BOOTSTRAP
#define RESOLVE_MAP(map, scope, sym, version, flags) map
#include "dynamic-link.h"

/* Must include after <dl-machine.h> for DT_MIPS definition.  */
#include <dl-debug.h>

/* Only enables rtld profiling for architectures which provides non generic
   hp-timing support.  The generic support requires either syscall
   (clock_gettime), which will incur in extra overhead on loading time.
   Using vDSO is also an option, but it will require extra support on loader
   to setup the vDSO pointer before its usage.  */
#if HP_TIMING_INLINE
# define RLTD_TIMING_DECLARE(var, classifier,...) \
  classifier hp_timing_t var __VA_ARGS__
# define RTLD_TIMING_VAR(var)        RLTD_TIMING_DECLARE (var, )
# define RTLD_TIMING_SET(var, value) (var) = (value)
# define RTLD_TIMING_REF(var)        &(var)

static inline void
rtld_timer_start (hp_timing_t *var)
{
  HP_TIMING_NOW (*var);
}

static inline void
rtld_timer_stop (hp_timing_t *var, hp_timing_t start)
{
  hp_timing_t stop;
  HP_TIMING_NOW (stop);
  HP_TIMING_DIFF (*var, start, stop);
}

static inline void
rtld_timer_accum (hp_timing_t *sum, hp_timing_t start)
{
  hp_timing_t stop;
  rtld_timer_stop (&stop, start);
  HP_TIMING_ACCUM_NT(*sum, stop);
}
#else
# define RLTD_TIMING_DECLARE(var, classifier...)
# define RTLD_TIMING_SET(var, value)
# define RTLD_TIMING_VAR(var)
# define RTLD_TIMING_REF(var)			 0
# define rtld_timer_start(var)
# define rtld_timer_stop(var, start)
# define rtld_timer_accum(sum, start)
#endif

/* Avoid PLT use for our local calls at startup.  */
extern __typeof (__mempcpy) __mempcpy attribute_hidden;

/* GCC has mental blocks about _exit.  */
extern __typeof (_exit) exit_internal asm ("_exit") attribute_hidden;
#define _exit exit_internal

/* Helper function to handle errors while resolving symbols.  */
static void print_unresolved (int errcode, const char *objname,
			      const char *errsting);

/* Helper function to handle errors when a version is missing.  */
static void print_missing_version (int errcode, const char *objname,
				   const char *errsting);

/* Print the various times we collected.  */
static void print_statistics (const hp_timing_t *total_timep);

/* Creates an empty audit list.  */
static void audit_list_init (struct audit_list *);

/* Add a string to the end of the audit list, for later parsing.  Must
   not be called after audit_list_next.  */
static void audit_list_add_string (struct audit_list *, const char *);

/* Add the audit strings from the link map, found in the dynamic
   segment at TG (either DT_AUDIT and DT_DEPAUDIT).  Must be called
   before audit_list_next.  */
static void audit_list_add_dynamic_tag (struct audit_list *,
					struct link_map *,
					unsigned int tag);

/* Extract the next audit module from the audit list.  Only modules
   for which dso_name_valid_for_suid is true are returned.  Must be
   called after all the audit_list_add_string,
   audit_list_add_dynamic_tags calls.  */
static const char *audit_list_next (struct audit_list *);

/* Initialize *STATE with the defaults.  */
static void dl_main_state_init (struct dl_main_state *state);

/* Process all environments variables the dynamic linker must recognize.
   Since all of them start with `LD_' we are a bit smarter while finding
   all the entries.  */
extern char **_environ attribute_hidden;
static void process_envvars (struct dl_main_state *state);

int _dl_argc attribute_relro attribute_hidden;
char **_dl_argv attribute_relro = NULL;
rtld_hidden_data_def (_dl_argv)

#ifndef THREAD_SET_STACK_GUARD
/* Only exported for architectures that don't store the stack guard canary
   in thread local area.  */
uintptr_t __stack_chk_guard attribute_relro;
#endif

/* Only exported for architectures that don't store the pointer guard
   value in thread local area.  */
uintptr_t __pointer_chk_guard_local attribute_relro attribute_hidden;
#ifndef THREAD_SET_POINTER_GUARD
strong_alias (__pointer_chk_guard_local, __pointer_chk_guard)
#endif

/* Check that AT_SECURE=0, or that the passed name does not contain
   directories and is not overly long.  Reject empty names
   unconditionally.  */
static bool
dso_name_valid_for_suid (const char *p)
{
  if (__glibc_unlikely (__libc_enable_secure))
    {
      /* Ignore pathnames with directories for AT_SECURE=1
	 programs, and also skip overlong names.  */
      size_t len = strlen (p);
      if (len >= SECURE_NAME_LIMIT || memchr (p, '/', len) != NULL)
	return false;
    }
  return *p != '\0';
}

static void
audit_list_init (struct audit_list *list)
{
  list->length = 0;
  list->current_index = 0;
  list->current_tail = NULL;
}

static void
audit_list_add_string (struct audit_list *list, const char *string)
{
  /* Empty strings do not load anything.  */
  if (*string == '\0')
    return;

  if (list->length == array_length (list->audit_strings))
    _dl_fatal_printf ("Fatal glibc error: Too many audit modules requested\n");

  list->audit_strings[list->length++] = string;

  /* Initialize processing of the first string for
     audit_list_next.  */
  if (list->length == 1)
    list->current_tail = string;
}

static void
audit_list_add_dynamic_tag (struct audit_list *list, struct link_map *main_map,
			    unsigned int tag)
{
  ElfW(Dyn) *info = main_map->l_info[ADDRIDX (tag)];
  const char *strtab = (const char *) D_PTR (main_map, l_info[DT_STRTAB]);
  if (info != NULL)
    audit_list_add_string (list, strtab + info->d_un.d_val);
}

static const char *
audit_list_next (struct audit_list *list)
{
  if (list->current_tail == NULL)
    return NULL;

  while (true)
    {
      /* Advance to the next string in audit_strings if the current
	 string has been exhausted.  */
      while (*list->current_tail == '\0')
	{
	  ++list->current_index;
	  if (list->current_index == list->length)
	    {
	      list->current_tail = NULL;
	      return NULL;
	    }
	  list->current_tail = list->audit_strings[list->current_index];
	}

      /* Split the in-string audit list at the next colon colon.  */
      size_t len = strcspn (list->current_tail, ":");
      if (len > 0 && len < sizeof (list->fname))
	{
	  memcpy (list->fname, list->current_tail, len);
	  list->fname[len] = '\0';
	}
      else
	/* Mark the name as unusable for dso_name_valid_for_suid.  */
	list->fname[0] = '\0';

      /* Skip over the substring and the following delimiter.  */
      list->current_tail += len;
      if (*list->current_tail == ':')
	++list->current_tail;

      /* If the name is valid, return it.  */
      if (dso_name_valid_for_suid (list->fname))
	return list->fname;

      /* Otherwise wrap around to find the next list element. .  */
    }
}

/* Count audit modules before they are loaded so GLRO(dl_naudit)
   is not yet usable.  */
static size_t
audit_list_count (struct audit_list *list)
{
  /* Restore the audit_list iterator state at the end.  */
  const char *saved_tail = list->current_tail;
  size_t naudit = 0;

  assert (list->current_index == 0);
  while (audit_list_next (list) != NULL)
    naudit++;
  list->current_tail = saved_tail;
  list->current_index = 0;
  return naudit;
}

static void
dl_main_state_init (struct dl_main_state *state)
{
  audit_list_init (&state->audit_list);
  state->library_path = NULL;
  state->library_path_source = NULL;
  state->preloadlist = NULL;
  state->preloadarg = NULL;
  state->glibc_hwcaps_prepend = NULL;
  state->glibc_hwcaps_mask = NULL;
  state->mode = rtld_mode_normal;
  state->any_debug = false;
  state->version_info = false;
}

#ifndef HAVE_INLINED_SYSCALLS
/* Set nonzero during loading and initialization of executable and
   libraries, cleared before the executable's entry point runs.  This
   must not be initialized to nonzero, because the unused dynamic
   linker loaded in for libc.so's "ld.so.1" dep will provide the
   definition seen by libc.so's initializer; that value must be zero,
   and will be since that dynamic linker's _dl_start and dl_main will
   never be called.  */
int _dl_starting_up = 0;
rtld_hidden_def (_dl_starting_up)
#endif

/* This is the structure which defines all variables global to ld.so
   (except those which cannot be added for some reason).  */
struct rtld_global _rtld_global =
  {
    /* Get architecture specific initializer.  */
#include <dl-procruntime.c>
    /* Generally the default presumption without further information is an
     * executable stack but this is not true for all platforms.  */
    ._dl_stack_flags = DEFAULT_STACK_PERMS,
#ifdef _LIBC_REENTRANT
    ._dl_load_lock = _RTLD_LOCK_RECURSIVE_INITIALIZER,
    ._dl_load_write_lock = _RTLD_LOCK_RECURSIVE_INITIALIZER,
    ._dl_load_tls_lock = _RTLD_LOCK_RECURSIVE_INITIALIZER,
#endif
    ._dl_nns = 1,
    ._dl_ns =
    {
#ifdef _LIBC_REENTRANT
      [LM_ID_BASE] = { ._ns_unique_sym_table
		       = { .lock = _RTLD_LOCK_RECURSIVE_INITIALIZER } }
#endif
    }
  };
/* If we would use strong_alias here the compiler would see a
   non-hidden definition.  This would undo the effect of the previous
   declaration.  So spell out what strong_alias does plus add the
   visibility attribute.  */
extern struct rtld_global _rtld_local
    __attribute__ ((alias ("_rtld_global"), visibility ("hidden")));


/* This variable is similar to _rtld_local, but all values are
   read-only after relocation.  */
struct rtld_global_ro _rtld_global_ro attribute_relro =
  {
    /* Get architecture specific initializer.  */
#include <dl-procinfo.c>
#ifdef NEED_DL_SYSINFO
    ._dl_sysinfo = DL_SYSINFO_DEFAULT,
#endif
    ._dl_debug_fd = STDERR_FILENO,
#if !HAVE_TUNABLES
    ._dl_hwcap_mask = HWCAP_IMPORTANT,
#endif
    ._dl_lazy = 1,
    ._dl_fpu_control = _FPU_DEFAULT,
    ._dl_pagesize = EXEC_PAGESIZE,
    ._dl_inhibit_cache = 0,

    /* Function pointers.  */
    ._dl_debug_printf = _dl_debug_printf,
    ._dl_mcount = _dl_mcount,
    ._dl_lookup_symbol_x = _dl_lookup_symbol_x,
    ._dl_open = _dl_open,
    ._dl_close = _dl_close,
    ._dl_catch_error = _rtld_catch_error,
    ._dl_error_free = _dl_error_free,
    ._dl_tls_get_addr_soft = _dl_tls_get_addr_soft,
    ._dl_libc_freeres = __rtld_libc_freeres,
  };
/* If we would use strong_alias here the compiler would see a
   non-hidden definition.  This would undo the effect of the previous
   declaration.  So spell out was strong_alias does plus add the
   visibility attribute.  */
extern struct rtld_global_ro _rtld_local_ro
    __attribute__ ((alias ("_rtld_global_ro"), visibility ("hidden")));


static void dl_main (const ElfW(Phdr) *phdr, ElfW(Word) phnum,
		     ElfW(Addr) *user_entry, ElfW(auxv_t) *auxv);

/* These two variables cannot be moved into .data.rel.ro.  */
static struct libname_list _dl_rtld_libname;
static struct libname_list _dl_rtld_libname2;

/* Variable for statistics.  */
RLTD_TIMING_DECLARE (relocate_time, static);
RLTD_TIMING_DECLARE (load_time,     static, attribute_relro);
RLTD_TIMING_DECLARE (start_time,    static, attribute_relro);

/* Additional definitions needed by TLS initialization.  */
#ifdef TLS_INIT_HELPER
TLS_INIT_HELPER
#endif

/* Helper function for syscall implementation.  */
#ifdef DL_SYSINFO_IMPLEMENTATION
DL_SYSINFO_IMPLEMENTATION
#endif

/* Before ld.so is relocated we must not access variables which need
   relocations.  This means variables which are exported.  Variables
   declared as static are fine.  If we can mark a variable hidden this
   is fine, too.  The latter is important here.  We can avoid setting
   up a temporary link map for ld.so if we can mark _rtld_global as
   hidden.  */
#ifndef HIDDEN_VAR_NEEDS_DYNAMIC_RELOC
# define DONT_USE_BOOTSTRAP_MAP	1
#endif

#ifdef DONT_USE_BOOTSTRAP_MAP
static ElfW(Addr) _dl_start_final (void *arg);
#else
struct dl_start_final_info
{
  struct link_map l;
  RTLD_TIMING_VAR (start_time);
};
static ElfW(Addr) _dl_start_final (void *arg,
				   struct dl_start_final_info *info);
#endif

/* These are defined magically by the linker.  */
extern const ElfW(Ehdr) __ehdr_start attribute_hidden;
extern char _etext[] attribute_hidden;
extern char _end[] attribute_hidden;


#ifdef RTLD_START
RTLD_START
#else
# error "sysdeps/MACHINE/dl-machine.h fails to define RTLD_START"
#endif

/* This is the second half of _dl_start (below).  It can be inlined safely
   under DONT_USE_BOOTSTRAP_MAP, where it is careful not to make any GOT
   references.  When the tools don't permit us to avoid using a GOT entry
   for _dl_rtld_global (no attribute_hidden support), we must make sure
   this function is not inlined (see below).  */

#ifdef DONT_USE_BOOTSTRAP_MAP
static inline ElfW(Addr) __attribute__ ((always_inline))
_dl_start_final (void *arg)
#else
static ElfW(Addr) __attribute__ ((noinline))
_dl_start_final (void *arg, struct dl_start_final_info *info)
#endif
{
  ElfW(Addr) start_addr;

  /* Do not use an initializer for these members because it would
     intefere with __rtld_static_init.  */
  GLRO (dl_find_object) = &_dl_find_object;

  /* If it hasn't happen yet record the startup time.  */
  rtld_timer_start (&start_time);
#if !defined DONT_USE_BOOTSTRAP_MAP
  RTLD_TIMING_SET (start_time, info->start_time);
#endif

  /* Transfer data about ourselves to the permanent link_map structure.  */
#ifndef DONT_USE_BOOTSTRAP_MAP
  GL(dl_rtld_map).l_addr = info->l.l_addr;
  GL(dl_rtld_map).l_ld = info->l.l_ld;
  GL(dl_rtld_map).l_ld_readonly = info->l.l_ld_readonly;
  memcpy (GL(dl_rtld_map).l_info, info->l.l_info,
	  sizeof GL(dl_rtld_map).l_info);
  GL(dl_rtld_map).l_mach = info->l.l_mach;
  GL(dl_rtld_map).l_relocated = 1;
#endif
  _dl_setup_hash (&GL(dl_rtld_map));
  GL(dl_rtld_map).l_real = &GL(dl_rtld_map);
  GL(dl_rtld_map).l_map_start = (ElfW(Addr)) &__ehdr_start;
  GL(dl_rtld_map).l_map_end = (ElfW(Addr)) _end;
  GL(dl_rtld_map).l_text_end = (ElfW(Addr)) _etext;
  /* Copy the TLS related data if necessary.  */
#ifndef DONT_USE_BOOTSTRAP_MAP
# if NO_TLS_OFFSET != 0
  GL(dl_rtld_map).l_tls_offset = NO_TLS_OFFSET;
# endif
#endif

  /* Initialize the stack end variable.  */
  __libc_stack_end = __builtin_frame_address (0);

  /* Call the OS-dependent function to set up life so we can do things like
     file access.  It will call `dl_main' (below) to do all the real work
     of the dynamic linker, and then unwind our frame and run the user
     entry point on the same stack we entered on.  */
  start_addr = _dl_sysdep_start (arg, &dl_main);

  if (__glibc_unlikely (GLRO(dl_debug_mask) & DL_DEBUG_STATISTICS))
    {
      RTLD_TIMING_VAR (rtld_total_time);
      rtld_timer_stop (&rtld_total_time, start_time);
      print_statistics (RTLD_TIMING_REF(rtld_total_time));
    }

#ifndef ELF_MACHINE_START_ADDRESS
# define ELF_MACHINE_START_ADDRESS(map, start) (start)
#endif
  return ELF_MACHINE_START_ADDRESS (GL(dl_ns)[LM_ID_BASE]._ns_loaded, start_addr);
}

#ifdef DONT_USE_BOOTSTRAP_MAP
# define bootstrap_map GL(dl_rtld_map)
#else
# define bootstrap_map info.l
#endif

static ElfW(Addr) __attribute_used__
_dl_start (void *arg)
{
#ifdef DONT_USE_BOOTSTRAP_MAP
  rtld_timer_start (&start_time);
#else
  struct dl_start_final_info info;
  rtld_timer_start (&info.start_time);
#endif

  /* Partly clean the `bootstrap_map' structure up.  Don't use
     `memset' since it might not be built in or inlined and we cannot
     make function calls at this point.  Use '__builtin_memset' if we
     know it is available.  We do not have to clear the memory if we
     do not have to use the temporary bootstrap_map.  Global variables
     are initialized to zero by default.  */
#ifndef DONT_USE_BOOTSTRAP_MAP
# ifdef HAVE_BUILTIN_MEMSET
  __builtin_memset (bootstrap_map.l_info, '\0', sizeof (bootstrap_map.l_info));
# else
  for (size_t cnt = 0;
       cnt < sizeof (bootstrap_map.l_info) / sizeof (bootstrap_map.l_info[0]);
       ++cnt)
    bootstrap_map.l_info[cnt] = 0;
# endif
#endif

  /* Figure out the run-time load address of the dynamic linker itself.  */
  bootstrap_map.l_addr = elf_machine_load_address ();

  /* Read our own dynamic section and fill in the info array.  */
  bootstrap_map.l_ld = (void *) bootstrap_map.l_addr + elf_machine_dynamic ();
  bootstrap_map.l_ld_readonly = DL_RO_DYN_SECTION;
  elf_get_dynamic_info (&bootstrap_map, true, false);

#if NO_TLS_OFFSET != 0
  bootstrap_map.l_tls_offset = NO_TLS_OFFSET;
#endif

#ifdef ELF_MACHINE_BEFORE_RTLD_RELOC
  ELF_MACHINE_BEFORE_RTLD_RELOC (&bootstrap_map, bootstrap_map.l_info);
#endif

  if (bootstrap_map.l_addr)
    {
      /* Relocate ourselves so we can do normal function calls and
	 data access using the global offset table.  */

      ELF_DYNAMIC_RELOCATE (&bootstrap_map, NULL, 0, 0, 0);
    }
  bootstrap_map.l_relocated = 1;

  /* Please note that we don't allow profiling of this object and
     therefore need not test whether we have to allocate the array
     for the relocation results (as done in dl-reloc.c).  */

  /* Now life is sane; we can call functions and access global data.
     Set up to use the operating system facilities, and find out from
     the operating system's program loader where to find the program
     header table in core.  Put the rest of _dl_start into a separate
     function, that way the compiler cannot put accesses to the GOT
     before ELF_DYNAMIC_RELOCATE.  */

  __rtld_malloc_init_stubs ();

#ifdef DONT_USE_BOOTSTRAP_MAP
  return _dl_start_final (arg);
#else
  return _dl_start_final (arg, &info);
#endif
}



/* Now life is peachy; we can do all normal operations.
   On to the real work.  */

/* Some helper functions.  */

/* Arguments to relocate_doit.  */
struct relocate_args
{
  struct link_map *l;
  int reloc_mode;
};

struct map_args
{
  /* Argument to map_doit.  */
  const char *str;
  struct link_map *loader;
  int mode;
  /* Return value of map_doit.  */
  struct link_map *map;
};

struct dlmopen_args
{
  const char *fname;
  struct link_map *map;
};

struct lookup_args
{
  const char *name;
  struct link_map *map;
  void *result;
};

/* Arguments to version_check_doit.  */
struct version_check_args
{
  int doexit;
  int dotrace;
};

static void
relocate_doit (void *a)
{
  struct relocate_args *args = (struct relocate_args *) a;

  _dl_relocate_object (args->l, args->l->l_scope, args->reloc_mode, 0);
}

static void
map_doit (void *a)
{
  struct map_args *args = (struct map_args *) a;
  int type = (args->mode == __RTLD_OPENEXEC) ? lt_executable : lt_library;
  args->map = _dl_map_object (args->loader, args->str, type, 0,
			      args->mode, LM_ID_BASE);
}

static void
dlmopen_doit (void *a)
{
  struct dlmopen_args *args = (struct dlmopen_args *) a;
  args->map = _dl_open (args->fname,
			(RTLD_LAZY | __RTLD_DLOPEN | __RTLD_AUDIT
			 | __RTLD_SECURE),
			dl_main, LM_ID_NEWLM, _dl_argc, _dl_argv,
			__environ);
}

static void
lookup_doit (void *a)
{
  struct lookup_args *args = (struct lookup_args *) a;
  const ElfW(Sym) *ref = NULL;
  args->result = NULL;
  lookup_t l = _dl_lookup_symbol_x (args->name, args->map, &ref,
				    args->map->l_local_scope, NULL, 0,
				    DL_LOOKUP_RETURN_NEWEST, NULL);
  if (ref != NULL)
    args->result = DL_SYMBOL_ADDRESS (l, ref);
}

static void
version_check_doit (void *a)
{
  struct version_check_args *args = (struct version_check_args *) a;
  if (_dl_check_all_versions (GL(dl_ns)[LM_ID_BASE]._ns_loaded, 1,
			      args->dotrace) && args->doexit)
    /* We cannot start the application.  Abort now.  */
    _exit (1);
}


static inline struct link_map *
find_needed (const char *name)
{
  struct r_scope_elem *scope = &GL(dl_ns)[LM_ID_BASE]._ns_loaded->l_searchlist;
  unsigned int n = scope->r_nlist;

  while (n-- > 0)
    if (_dl_name_match_p (name, scope->r_list[n]))
      return scope->r_list[n];

  /* Should never happen.  */
  return NULL;
}

static int
match_version (const char *string, struct link_map *map)
{
  const char *strtab = (const void *) D_PTR (map, l_info[DT_STRTAB]);
  ElfW(Verdef) *def;

#define VERDEFTAG (DT_NUM + DT_THISPROCNUM + DT_VERSIONTAGIDX (DT_VERDEF))
  if (map->l_info[VERDEFTAG] == NULL)
    /* The file has no symbol versioning.  */
    return 0;

  def = (ElfW(Verdef) *) ((char *) map->l_addr
			  + map->l_info[VERDEFTAG]->d_un.d_ptr);
  while (1)
    {
      ElfW(Verdaux) *aux = (ElfW(Verdaux) *) ((char *) def + def->vd_aux);

      /* Compare the version strings.  */
      if (strcmp (string, strtab + aux->vda_name) == 0)
	/* Bingo!  */
	return 1;

      /* If no more definitions we failed to find what we want.  */
      if (def->vd_next == 0)
	break;

      /* Next definition.  */
      def = (ElfW(Verdef) *) ((char *) def + def->vd_next);
    }

  return 0;
}

static bool tls_init_tp_called;

static void *
init_tls (size_t naudit)
{
  /* Number of elements in the static TLS block.  */
  GL(dl_tls_static_nelem) = GL(dl_tls_max_dtv_idx);

  /* Do not do this twice.  The audit interface might have required
     the DTV interfaces to be set up early.  */
  if (GL(dl_initial_dtv) != NULL)
    return NULL;

  /* Allocate the array which contains the information about the
     dtv slots.  We allocate a few entries more than needed to
     avoid the need for reallocation.  */
  size_t nelem = GL(dl_tls_max_dtv_idx) + 1 + TLS_SLOTINFO_SURPLUS;

  /* Allocate.  */
  GL(dl_tls_dtv_slotinfo_list) = (struct dtv_slotinfo_list *)
    calloc (sizeof (struct dtv_slotinfo_list)
	    + nelem * sizeof (struct dtv_slotinfo), 1);
  /* No need to check the return value.  If memory allocation failed
     the program would have been terminated.  */

  struct dtv_slotinfo *slotinfo = GL(dl_tls_dtv_slotinfo_list)->slotinfo;
  GL(dl_tls_dtv_slotinfo_list)->len = nelem;
  GL(dl_tls_dtv_slotinfo_list)->next = NULL;

  /* Fill in the information from the loaded modules.  No namespace
     but the base one can be filled at this time.  */
  assert (GL(dl_ns)[LM_ID_BASE + 1]._ns_loaded == NULL);
  int i = 0;
  for (struct link_map *l = GL(dl_ns)[LM_ID_BASE]._ns_loaded; l != NULL;
       l = l->l_next)
    if (l->l_tls_blocksize != 0)
      {
	/* This is a module with TLS data.  Store the map reference.
	   The generation counter is zero.  */
	slotinfo[i].map = l;
	/* slotinfo[i].gen = 0; */
	++i;
      }
  assert (i == GL(dl_tls_max_dtv_idx));

  /* Calculate the size of the static TLS surplus.  */
  _dl_tls_static_surplus_init (naudit);

  /* Compute the TLS offsets for the various blocks.  */
  _dl_determine_tlsoffset ();

  /* Construct the static TLS block and the dtv for the initial
     thread.  For some platforms this will include allocating memory
     for the thread descriptor.  The memory for the TLS block will
     never be freed.  It should be allocated accordingly.  The dtv
     array can be changed if dynamic loading requires it.  */
  void *tcbp = _dl_allocate_tls_storage ();
  if (tcbp == NULL)
    _dl_fatal_printf ("\
cannot allocate TLS data structures for initial thread\n");

  /* Store for detection of the special case by __tls_get_addr
     so it knows not to pass this dtv to the normal realloc.  */
  GL(dl_initial_dtv) = GET_DTV (tcbp);

  /* And finally install it for the main thread.  */
  const char *lossage = TLS_INIT_TP (tcbp);
  if (__glibc_unlikely (lossage != NULL))
    _dl_fatal_printf ("cannot set up thread-local storage: %s\n", lossage);
  __tls_init_tp ();
  tls_init_tp_called = true;

  return tcbp;
}

static unsigned int
do_preload (const char *fname, struct link_map *main_map, const char *where)
{
  const char *objname;
  const char *err_str = NULL;
  struct map_args args;
  bool malloced;

  args.str = fname;
  args.loader = main_map;
  args.mode = __RTLD_SECURE;

  unsigned int old_nloaded = GL(dl_ns)[LM_ID_BASE]._ns_nloaded;

  (void) _dl_catch_error (&objname, &err_str, &malloced, map_doit, &args);
  if (__glibc_unlikely (err_str != NULL))
    {
      _dl_error_printf ("\
ERROR: ld.so: object '%s' from %s cannot be preloaded (%s): ignored.\n",
			fname, where, err_str);
      /* No need to call free, this is still before
	 the libc's malloc is used.  */
    }
  else if (GL(dl_ns)[LM_ID_BASE]._ns_nloaded != old_nloaded)
    /* It is no duplicate.  */
    return 1;

  /* Nothing loaded.  */
  return 0;
}

static void
security_init (void)
{
  /* Set up the stack checker's canary.  */
  uintptr_t stack_chk_guard = _dl_setup_stack_chk_guard (_dl_random);
#ifdef THREAD_SET_STACK_GUARD
  THREAD_SET_STACK_GUARD (stack_chk_guard);
#else
  __stack_chk_guard = stack_chk_guard;
#endif

  /* Set up the pointer guard as well, if necessary.  */
  uintptr_t pointer_chk_guard
    = _dl_setup_pointer_guard (_dl_random, stack_chk_guard);
#ifdef THREAD_SET_POINTER_GUARD
  THREAD_SET_POINTER_GUARD (pointer_chk_guard);
#endif
  __pointer_chk_guard_local = pointer_chk_guard;

  /* We do not need the _dl_random value anymore.  The less
     information we leave behind, the better, so clear the
     variable.  */
  _dl_random = NULL;
}

#include <setup-vdso.h>

/* The LD_PRELOAD environment variable gives list of libraries
   separated by white space or colons that are loaded before the
   executable's dependencies and prepended to the global scope list.
   (If the binary is running setuid all elements containing a '/' are
   ignored since it is insecure.)  Return the number of preloads
   performed.   Ditto for --preload command argument.  */
unsigned int
handle_preload_list (const char *preloadlist, struct link_map *main_map,
		     const char *where)
{
  unsigned int npreloads = 0;
  const char *p = preloadlist;
  char fname[SECURE_PATH_LIMIT];

  while (*p != '\0')
    {
      /* Split preload list at space/colon.  */
      size_t len = strcspn (p, " :");
      if (len > 0 && len < sizeof (fname))
	{
	  memcpy (fname, p, len);
	  fname[len] = '\0';
	}
      else
	fname[0] = '\0';

      /* Skip over the substring and the following delimiter.  */
      p += len;
      if (*p != '\0')
	++p;

      if (dso_name_valid_for_suid (fname))
	npreloads += do_preload (fname, main_map, where);
    }
  return npreloads;
}

/* Called if the audit DSO cannot be used: if it does not have the
   appropriate interfaces, or it expects a more recent version library
   version than what the dynamic linker provides.  */
static void
unload_audit_module (struct link_map *map, int original_tls_idx)
{
#ifndef NDEBUG
  Lmid_t ns = map->l_ns;
#endif
  _dl_close (map);

  /* Make sure the namespace has been cleared entirely.  */
  assert (GL(dl_ns)[ns]._ns_loaded == NULL);
  assert (GL(dl_ns)[ns]._ns_nloaded == 0);

  GL(dl_tls_max_dtv_idx) = original_tls_idx;
}

/* Called to print an error message if loading of an audit module
   failed.  */
static void
report_audit_module_load_error (const char *name, const char *err_str,
				bool malloced)
{
  _dl_error_printf ("\
ERROR: ld.so: object '%s' cannot be loaded as audit interface: %s; ignored.\n",
		    name, err_str);
  if (malloced)
    free ((char *) err_str);
}

/* Load one audit module.  */
static void
load_audit_module (const char *name, struct audit_ifaces **last_audit)
{
  int original_tls_idx = GL(dl_tls_max_dtv_idx);

  struct dlmopen_args dlmargs;
  dlmargs.fname = name;
  dlmargs.map = NULL;

  const char *objname;
  const char *err_str = NULL;
  bool malloced;
  _dl_catch_error (&objname, &err_str, &malloced, dlmopen_doit, &dlmargs);
  if (__glibc_unlikely (err_str != NULL))
    {
      report_audit_module_load_error (name, err_str, malloced);
      return;
    }

  struct lookup_args largs;
  largs.name = "la_version";
  largs.map = dlmargs.map;
  _dl_catch_error (&objname, &err_str, &malloced, lookup_doit, &largs);
  if (__glibc_likely (err_str != NULL))
    {
      unload_audit_module (dlmargs.map, original_tls_idx);
      report_audit_module_load_error (name, err_str, malloced);
      return;
    }

  unsigned int (*laversion) (unsigned int) = largs.result;

 /* A null symbol indicates that something is very wrong with the
    loaded object because defined symbols are supposed to have a
    valid, non-null address.  */
  assert (laversion != NULL);

  unsigned int lav = laversion (LAV_CURRENT);
  if (lav == 0)
    {
      /* Only print an error message if debugging because this can
	 happen deliberately.  */
      if (GLRO(dl_debug_mask) & DL_DEBUG_FILES)
	_dl_debug_printf ("\
file=%s [%lu]; audit interface function la_version returned zero; ignored.\n",
			  dlmargs.map->l_name, dlmargs.map->l_ns);
      unload_audit_module (dlmargs.map, original_tls_idx);
      return;
    }

  if (!_dl_audit_check_version (lav))
    {
      _dl_debug_printf ("\
ERROR: audit interface '%s' requires version %d (maximum supported version %d); ignored.\n",
			name, lav, LAV_CURRENT);
      unload_audit_module (dlmargs.map, original_tls_idx);
      return;
    }

  enum { naudit_ifaces = 8 };
  union
  {
    struct audit_ifaces ifaces;
    void (*fptr[naudit_ifaces]) (void);
  } *newp = malloc (sizeof (*newp));
  if (newp == NULL)
    _dl_fatal_printf ("Out of memory while loading audit modules\n");

  /* Names of the auditing interfaces.  All in one
     long string.  */
  static const char audit_iface_names[] =
    "la_activity\0"
    "la_objsearch\0"
    "la_objopen\0"
    "la_preinit\0"
    LA_SYMBIND "\0"
#define STRING(s) __STRING (s)
    "la_" STRING (ARCH_LA_PLTENTER) "\0"
    "la_" STRING (ARCH_LA_PLTEXIT) "\0"
    "la_objclose\0";
  unsigned int cnt = 0;
  const char *cp = audit_iface_names;
  do
    {
      largs.name = cp;
      _dl_catch_error (&objname, &err_str, &malloced, lookup_doit, &largs);

      /* Store the pointer.  */
      if (err_str == NULL && largs.result != NULL)
	newp->fptr[cnt] = largs.result;
      else
	newp->fptr[cnt] = NULL;
      ++cnt;

      cp = rawmemchr (cp, '\0') + 1;
    }
  while (*cp != '\0');
  assert (cnt == naudit_ifaces);

  /* Now append the new auditing interface to the list.  */
  newp->ifaces.next = NULL;
  if (*last_audit == NULL)
    *last_audit = GLRO(dl_audit) = &newp->ifaces;
  else
    *last_audit = (*last_audit)->next = &newp->ifaces;

  /* The dynamic linker link map is statically allocated, so the
     cookie in _dl_new_object has not happened.  */
  link_map_audit_state (&GL (dl_rtld_map), GLRO (dl_naudit))->cookie
    = (intptr_t) &GL (dl_rtld_map);

  ++GLRO(dl_naudit);

  /* Mark the DSO as being used for auditing.  */
  dlmargs.map->l_auditing = 1;
}

/* Load all audit modules.  */
static void
load_audit_modules (struct link_map *main_map, struct audit_list *audit_list)
{
  struct audit_ifaces *last_audit = NULL;

  while (true)
    {
      const char *name = audit_list_next (audit_list);
      if (name == NULL)
	break;
      load_audit_module (name, &last_audit);
    }

  /* Notify audit modules of the initially loaded modules (the main
     program and the dynamic linker itself).  */
  if (GLRO(dl_naudit) > 0)
    {
      _dl_audit_objopen (main_map, LM_ID_BASE);
      _dl_audit_objopen (&GL(dl_rtld_map), LM_ID_BASE);
    }
}

/* Check if the executable is not actualy dynamically linked, and
   invoke it directly in that case.  */
static void
rtld_chain_load (struct link_map *main_map, char *argv0)
{
  /* The dynamic loader run against itself.  */
  const char *rtld_soname
    = ((const char *) D_PTR (&GL(dl_rtld_map), l_info[DT_STRTAB])
       + GL(dl_rtld_map).l_info[DT_SONAME]->d_un.d_val);
  if (main_map->l_info[DT_SONAME] != NULL
      && strcmp (rtld_soname,
		 ((const char *) D_PTR (main_map, l_info[DT_STRTAB])
		  + main_map->l_info[DT_SONAME]->d_un.d_val)) == 0)
    _dl_fatal_printf ("%s: loader cannot load itself\n", rtld_soname);

  /* With DT_NEEDED dependencies, the executable is dynamically
     linked.  */
  if (__glibc_unlikely (main_map->l_info[DT_NEEDED] != NULL))
    return;

  /* If the executable has program interpreter, it is dynamically
     linked.  */
  for (size_t i = 0; i < main_map->l_phnum; ++i)
    if (main_map->l_phdr[i].p_type == PT_INTERP)
      return;

  const char *pathname = _dl_argv[0];
  if (argv0 != NULL)
    _dl_argv[0] = argv0;
  int errcode = __rtld_execve (pathname, _dl_argv, _environ);
  const char *errname = strerrorname_np (errcode);
  if (errname != NULL)
    _dl_fatal_printf("%s: cannot execute %s: %s\n",
		     rtld_soname, pathname, errname);
  else
    _dl_fatal_printf("%s: cannot execute %s: %d\n",
		     rtld_soname, pathname, errcode);
}

/* Called to complete the initialization of the link map for the main
   executable.  Returns true if there is a PT_INTERP segment.  */
static bool
rtld_setup_main_map (struct link_map *main_map)
{
  /* This have already been filled in right after _dl_new_object, or
     as part of _dl_map_object.  */
  const ElfW(Phdr) *phdr = main_map->l_phdr;
  ElfW(Word) phnum = main_map->l_phnum;

  bool has_interp = false;

  main_map->l_map_end = 0;
  main_map->l_text_end = 0;
  /* Perhaps the executable has no PT_LOAD header entries at all.  */
  main_map->l_map_start = ~0;
  /* And it was opened directly.  */
  ++main_map->l_direct_opencount;
  main_map->l_contiguous = 1;

  /* A PT_LOAD segment at an unexpected address will clear the
     l_contiguous flag.  The ELF specification says that PT_LOAD
     segments need to be sorted in in increasing order, but perhaps
     not all executables follow this requirement.  Having l_contiguous
     equal to 1 is just an optimization, so the code below does not
     try to sort the segments in case they are unordered.

     There is one corner case in which l_contiguous is not set to 1,
     but where it could be set: If a PIE (ET_DYN) binary is loaded by
     glibc itself (not the kernel), it is always contiguous due to the
     way the glibc loader works.  However, the kernel loader may still
     create holes in this case, and the code here still uses 0
     conservatively for the glibc-loaded case, too.  */
  ElfW(Addr) expected_load_address = 0;

  /* Scan the program header table for the dynamic section.  */
  for (const ElfW(Phdr) *ph = phdr; ph < &phdr[phnum]; ++ph)
    switch (ph->p_type)
      {
      case PT_PHDR:
	/* Find out the load address.  */
	main_map->l_addr = (ElfW(Addr)) phdr - ph->p_vaddr;
	break;
      case PT_DYNAMIC:
	/* This tells us where to find the dynamic section,
	   which tells us everything we need to do.  */
	main_map->l_ld = (void *) main_map->l_addr + ph->p_vaddr;
	main_map->l_ld_readonly = (ph->p_flags & PF_W) == 0;
	break;
      case PT_INTERP:
	/* This "interpreter segment" was used by the program loader to
	   find the program interpreter, which is this program itself, the
	   dynamic linker.  We note what name finds us, so that a future
	   dlopen call or DT_NEEDED entry, for something that wants to link
	   against the dynamic linker as a shared library, will know that
	   the shared object is already loaded.  */
	_dl_rtld_libname.name = ((const char *) main_map->l_addr
				 + ph->p_vaddr);
	/* _dl_rtld_libname.next = NULL;	Already zero.  */
	GL(dl_rtld_map).l_libname = &_dl_rtld_libname;

	/* Ordinarilly, we would get additional names for the loader from
	   our DT_SONAME.  This can't happen if we were actually linked as
	   a static executable (detect this case when we have no DYNAMIC).
	   If so, assume the filename component of the interpreter path to
	   be our SONAME, and add it to our name list.  */
	if (GL(dl_rtld_map).l_ld == NULL)
	  {
	    const char *p = NULL;
	    const char *cp = _dl_rtld_libname.name;

	    /* Find the filename part of the path.  */
	    while (*cp != '\0')
	      if (*cp++ == '/')
		p = cp;

	    if (p != NULL)
	      {
		_dl_rtld_libname2.name = p;
		/* _dl_rtld_libname2.next = NULL;  Already zero.  */
		_dl_rtld_libname.next = &_dl_rtld_libname2;
	      }
	  }

	has_interp = true;
	break;
      case PT_LOAD:
	{
	  ElfW(Addr) mapstart;
	  ElfW(Addr) allocend;

	  /* Remember where the main program starts in memory.  */
	  mapstart = (main_map->l_addr
		      + (ph->p_vaddr & ~(GLRO(dl_pagesize) - 1)));
	  if (main_map->l_map_start > mapstart)
	    main_map->l_map_start = mapstart;

	  if (main_map->l_contiguous && expected_load_address != 0
	      && expected_load_address != mapstart)
	    main_map->l_contiguous = 0;

	  /* Also where it ends.  */
	  allocend = main_map->l_addr + ph->p_vaddr + ph->p_memsz;
	  if (main_map->l_map_end < allocend)
	    main_map->l_map_end = allocend;
	  if ((ph->p_flags & PF_X) && allocend > main_map->l_text_end)
	    main_map->l_text_end = allocend;

	  /* The next expected address is the page following this load
	     segment.  */
	  expected_load_address = ((allocend + GLRO(dl_pagesize) - 1)
				   & ~(GLRO(dl_pagesize) - 1));
	}
	break;

      case PT_TLS:
	if (ph->p_memsz > 0)
	  {
	    /* Note that in the case the dynamic linker we duplicate work
	       here since we read the PT_TLS entry already in
	       _dl_start_final.  But the result is repeatable so do not
	       check for this special but unimportant case.  */
	    main_map->l_tls_blocksize = ph->p_memsz;
	    main_map->l_tls_align = ph->p_align;
	    if (ph->p_align == 0)
	      main_map->l_tls_firstbyte_offset = 0;
	    else
	      main_map->l_tls_firstbyte_offset = (ph->p_vaddr
						  & (ph->p_align - 1));
	    main_map->l_tls_initimage_size = ph->p_filesz;
	    main_map->l_tls_initimage = (void *) ph->p_vaddr;

	    /* This image gets the ID one.  */
	    GL(dl_tls_max_dtv_idx) = main_map->l_tls_modid = 1;
	  }
	break;

      case PT_GNU_STACK:
	GL(dl_stack_flags) = ph->p_flags;
	break;

      case PT_GNU_RELRO:
	main_map->l_relro_addr = ph->p_vaddr;
	main_map->l_relro_size = ph->p_memsz;
	break;
      }
  /* Process program headers again, but scan them backwards so
     that PT_NOTE can be skipped if PT_GNU_PROPERTY exits.  */
  for (const ElfW(Phdr) *ph = &phdr[phnum]; ph != phdr; --ph)
    switch (ph[-1].p_type)
      {
      case PT_NOTE:
	_dl_process_pt_note (main_map, -1, &ph[-1]);
	break;
      case PT_GNU_PROPERTY:
	_dl_process_pt_gnu_property (main_map, -1, &ph[-1]);
	break;
      }

  /* Adjust the address of the TLS initialization image in case
     the executable is actually an ET_DYN object.  */
  if (main_map->l_tls_initimage != NULL)
    main_map->l_tls_initimage
      = (char *) main_map->l_tls_initimage + main_map->l_addr;
  if (! main_map->l_map_end)
    main_map->l_map_end = ~0;
  if (! main_map->l_text_end)
    main_map->l_text_end = ~0;
  if (! GL(dl_rtld_map).l_libname && GL(dl_rtld_map).l_name)
    {
      /* We were invoked directly, so the program might not have a
	 PT_INTERP.  */
      _dl_rtld_libname.name = GL(dl_rtld_map).l_name;
      /* _dl_rtld_libname.next = NULL;	Already zero.  */
      GL(dl_rtld_map).l_libname =  &_dl_rtld_libname;
    }
  else
    assert (GL(dl_rtld_map).l_libname); /* How else did we get here?  */

  return has_interp;
}

/* Adjusts the contents of the stack and related globals for the user
   entry point.  The ld.so processed skip_args arguments and bumped
   _dl_argv and _dl_argc accordingly.  Those arguments are removed from
   argv here.  */
static void
_dl_start_args_adjust (int skip_args)
{
  void **sp = (void **) (_dl_argv - skip_args - 1);
  void **p = sp + skip_args;

  if (skip_args == 0)
    return;

  /* Sanity check.  */
  intptr_t argc __attribute__ ((unused)) = (intptr_t) sp[0] - skip_args;
  assert (argc == _dl_argc);

  /* Adjust argc on stack.  */
  sp[0] = (void *) (intptr_t) _dl_argc;

  /* Update globals in rtld.  */
  _dl_argv -= skip_args;
  _environ -= skip_args;

  /* Shuffle argv down.  */
  do
    *++sp = *++p;
  while (*p != NULL);

  assert (_environ == (char **) (sp + 1));

  /* Shuffle envp down.  */
  do
    *++sp = *++p;
  while (*p != NULL);

#ifdef HAVE_AUX_VECTOR
  void **auxv = (void **) GLRO(dl_auxv) - skip_args;
  GLRO(dl_auxv) = (ElfW(auxv_t) *) auxv; /* Aliasing violation.  */
  assert (auxv == sp + 1);

  /* Shuffle auxv down. */
  ElfW(auxv_t) ax;
  char *oldp = (char *) (p + 1);
  char *newp = (char *) (sp + 1);
  do
    {
      memcpy (&ax, oldp, sizeof (ax));
      memcpy (newp, &ax, sizeof (ax));
      oldp += sizeof (ax);
      newp += sizeof (ax);
    }
  while (ax.a_type != AT_NULL);
#endif
}

#include <signal.h>
#include <ucontext.h>
#include <linux/limits.h>
#include <sys/resource.h>
#include <sys/un.h>
#include <sys/socket.h>
#include <sigrpc.h>

static void serialize_header(void *buf, rpc_msg_header_t header)
{
  int offset = 0;
  memcpy(buf + offset, &header.msg_type, sizeof(header.msg_type));
  offset += sizeof(header.msg_type);
  memcpy(buf + offset, &header.status, sizeof(header.status));
  offset += sizeof(header.status);
  memcpy(buf + offset, &header.client_id, sizeof(header.client_id));
  offset += sizeof(header.client_id);
  memcpy(buf + offset, &header.payload_size, sizeof(header.payload_size));
}

static rpc_msg_header_t deserialize_header(void *buf)
{
  rpc_msg_header_t header = {0};
  int offset = 0;
  memcpy(&header.msg_type, buf + offset, sizeof(header.msg_type));
  offset += sizeof(header.msg_type);
  memcpy(&header.status, buf + offset, sizeof(header.status));
  offset += sizeof(header.status);
  memcpy(&header.client_id, buf + offset, sizeof(header.client_id));
  offset += sizeof(header.client_id);
  memcpy(&header.payload_size, buf + offset, sizeof(header.payload_size));
  return header;
}

static void make_shift(unsigned long *shift, const char *ptrn, unsigned long ptrn_len)
{
    unsigned long *border_position = alloca((ptrn_len + 1) * sizeof(unsigned long));
    unsigned long i = ptrn_len;
    unsigned long j = i + 1;
    border_position[i] = j;

    while (i > 0)
    {
        while (j <= ptrn_len && ptrn[i - 1] != ptrn[j - 1])
        {
            if (shift[j] == 0)
                shift[j] = j - i;
            j = border_position[j];
        }
        i--;
        j--;
        border_position[i] = j;
    }

    j = border_position[0];
    for (i = 0;i <= ptrn_len; i++)
    {
        if (shift[i] == 0)
            shift[i] = j;
        
        if (i == j)
            j = border_position[j];
    }
}

static char *bm_search(const char *target, const char *ptrn)
{
    const unsigned long ptrn_len = __builtin_strlen(ptrn);
    unsigned long *shift = alloca((ptrn_len + 1) * sizeof(unsigned long));

    __builtin_memset(shift, 0, (ptrn_len + 1) * sizeof(unsigned long));
    make_shift(shift, ptrn, ptrn_len);

    while (__builtin_strlen(target) >= ptrn_len)
    {
        const char *c1 = target + ptrn_len - 1;
        const char *c2 = ptrn + ptrn_len - 1;
        while (c1 >= target && *c1 == *c2)
        {
            c1--;
            c2--;
        }
        if (c1 < target)
            return (char *)target;
        target += shift[c1 - target + 1];
    }
    return NULL;
}

static int want_rpc(const char *file)
{
  char *ld_rpc = getenv("LD_RPC");
  char *rpc_sock_path = getenv("RPC_SOCK_PATH");
  char *subst = NULL;
  struct stat buf = {0};

  if (!file)
    return 0;

  if (!ld_rpc || !rpc_sock_path)
	  return 0;
  if (stat(rpc_sock_path, &buf) == -1)
	  return 0;
  if (strlen(file) == 0)
    return 0;
  if ((subst = bm_search(ld_rpc, file)))
  {
	  switch (*(subst - 1))
	  {
	  case '=':
	  case ':':
	    break;
    case '/':
	    if (!strncmp(subst, file, strlen(file)))
      {
        char *_subst = subst - 1;
        while (*_subst == '/')
          _subst--;
        switch (*_subst)
        {
        case '=':
        case ':':
          break;
        default:
          return 0;
        }
      }
      break;
	  default:
	    return 0;
	  }
	  switch (*(subst + strlen(subst)))
	  {
	  case '\0':
	  case ':':
      return 1;
	  }
  }
  return 0;
}

static int connect_rpc_sock(void)
{
  char *rpc_sock_path = getenv("RPC_SOCK_PATH");
  struct stat buf = {0};

  if (!rpc_sock_path)
	  return -1;
  if (stat(rpc_sock_path, &buf) == -1)
	  return -1;
  int fd;
  struct sockaddr_un addr = {0};
  addr.sun_family = AF_UNIX;
  memcpy(addr.sun_path, rpc_sock_path, strlen(rpc_sock_path));
  if ((fd = socket(AF_UNIX, SOCK_STREAM, 0)) < 0)
    INLINE_SYSCALL(exit, 1, errno);
  if (connect(fd, (struct sockaddr *)&addr,
      sizeof(struct sockaddr_un)) < 0)
    INLINE_SYSCALL(exit, 1, errno);
  return fd;
}

__rtld_lock_define_recursive(static, stderr_mtx);

typedef struct successor_list_s {
  struct successor_list_s *prev;
  struct successor_list_s *next;
  uint64_t runtime_revision;
  int fd;
} successor_list_t;

typedef struct page_s {
  uint64_t address;
  uint64_t wr_addr;
  uint64_t runtime_revision;
  uint64_t client_revision;
  void *content;
  successor_list_t *successor_list;
  struct page_s *prev;
  struct page_s *next;
  uint64_t stack_ptr;
  uint32_t size;
} page_t;

typedef struct page_chain_s {
  page_t *page;
  struct page_chain_s *prev;
  struct page_chain_s *next;
} page_chain_t;

typedef struct page_tbl_s {
  page_t *page_list;
  page_chain_t **page_hash_tbl;
  uint64_t invokefunc_id;
  __rtld_lock_define_recursive(, lock);
} page_tbl_t;

static page_tbl_t page_tbl;

static void init_page_tbl(void)
{
  page_tbl.page_hash_tbl = calloc(1 << 16, sizeof(page_chain_t *));
  if (!page_tbl.page_hash_tbl)
    INLINE_SYSCALL(exit, 1, errno);
  __rtld_lock_initialize(page_tbl.lock);
}

static void lock_page_tbl(void)
{
  __rtld_lock_lock_recursive(page_tbl.lock);
}

static void unlock_page_tbl(void)
{
  __rtld_lock_unlock_recursive(page_tbl.lock);
}

typedef struct curr_page_s {
  void *curr_page;
  __rtld_lock_define_recursive(, lock);
} curr_page_t;

static curr_page_t curr_page;

static void init_curr_page(void)
{
  __rtld_lock_initialize(curr_page.lock);
}

static void lock_curr_page(void)
{
  __rtld_lock_lock_recursive(curr_page.lock);
}

static void unlock_curr_page(void)
{
  __rtld_lock_unlock_recursive(curr_page.lock);
}

static uint64_t calc_page_hash_tbl_idx(uint64_t addr)
{
  uint64_t key = addr >> 12;
  uint64_t hash_mask = (1 << 16) - 1;
  return key & hash_mask;
}

static page_chain_t *search_page_in_chain(page_chain_t *chain, uint64_t addr)
{
  addr &= 0xfffffffffffff000;
  if (!chain)
    return NULL;
  while (chain && chain->page->address != addr)
    chain = chain->next;
  return chain;
}

static void add_page_list(page_t *entry)
{
  entry->prev = NULL;
  entry->next = page_tbl.page_list;
  if (entry->next)
    entry->next->prev = entry;
  page_tbl.page_list = entry;
}

static void add_page_hashtbl_entry(page_t *entry)
{
  uint64_t idx = calc_page_hash_tbl_idx(entry->address);
  page_chain_t *new_entry = malloc(sizeof(page_chain_t));
  if (!new_entry)
    INLINE_SYSCALL(exit, 1, errno);
  new_entry->prev = NULL;
  new_entry->next = page_tbl.page_hash_tbl[idx];
  if (new_entry->next)
    new_entry->next->prev = new_entry;
  new_entry->page = entry;
  page_tbl.page_hash_tbl[idx] = new_entry;
}

static void add_page(page_t *entry)
{
  add_page_list(entry);
  add_page_hashtbl_entry(entry);
}

static void remove_page(uint64_t addr)
{
  uint64_t idx = calc_page_hash_tbl_idx(addr);
  page_chain_t *chain = page_tbl.page_hash_tbl[idx];
  chain = search_page_in_chain(chain, addr);
  if (!chain)
    return;
  page_t *entry = chain->page;
  if (entry->prev)
    entry->prev->next = entry->next;
  else
    page_tbl.page_list = entry->next;
  if (entry->next)
    entry->next->prev = entry->prev;

  if (chain->prev)
    chain->prev->next = chain->next;
  else
    page_tbl.page_hash_tbl[idx] = chain->next;
  if (chain->next)
    chain->next->prev = chain->prev;
  free(chain);
  free(entry->content);
  munmap((void *)entry->address, entry->size);
  munmap((void *)entry->wr_addr, entry->size);
  free(entry);
}

static page_t *get_page(uint64_t addr)
{
  uint64_t idx = calc_page_hash_tbl_idx(addr);
  page_chain_t *chain = search_page_in_chain(page_tbl.page_hash_tbl[idx], addr);
  if (chain)
    return chain->page;
  return NULL;
}

static void wait_prev_revision(uint64_t addr, uint64_t runtime_revision)
{
  uint64_t buf;
  int fds[2];
  page_t *page = get_page(addr);
  assert(page);
  if (page->runtime_revision + 1 >= runtime_revision)
    return;
  successor_list_t suc = {0};
  suc.next = page->successor_list;
  page->successor_list = &suc;
  if (suc.next)
    suc.next->prev = &suc;
  if (pipe(fds) == -1)
    INLINE_SYSCALL(exit, 1, errno);
  suc.fd = fds[1];
  unlock_page_tbl();
  if (read(fds[0], &buf, sizeof(buf)) == -1)
    INLINE_SYSCALL(exit, 1, errno);
  lock_page_tbl();
  close(fds[0]);
  close(fds[1]);
  if (suc.prev)
    suc.prev->next = suc.next;
  if (suc.next)
    suc.next->prev = suc.prev;
  if (!suc.prev)
    page->successor_list = suc.next;
}

static void notify_successor(uint64_t addr, uint64_t curr_runtime_revision)
{
  page_t *page = get_page(addr);
  assert(page);
  successor_list_t *suc_iter = page->successor_list;
  while (suc_iter)
  {
    if (suc_iter->runtime_revision == 0 ||\
        suc_iter->runtime_revision == curr_runtime_revision + 1)
      if (write(suc_iter->fd, &curr_runtime_revision,
          sizeof(curr_runtime_revision)) == -1)
        INLINE_SYSCALL(exit, 1, errno);
    suc_iter = suc_iter->next;
  }
}

static void *page_exist(void *addr, uint64_t size)
{
  void *map_addr = mmap(addr, size, PROT_NONE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  if (map_addr == MAP_FAILED)
    INLINE_SYSCALL(exit, 1, errno);
  munmap(map_addr, size);
  if (map_addr == addr)
    return MAP_FAILED;
  return addr;
}

typedef struct msg_buf_s {
  uint8_t *buf;
  uint64_t size;
  uint64_t cap;
} msg_buf_t;

static msg_buf_t make_msg_buf(uint64_t cap)
{
  msg_buf_t buf = {0};
  buf.buf = mmap(NULL, cap, PROT_WRITE | PROT_READ, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (buf.buf == MAP_FAILED)
    INLINE_SYSCALL(exit, 1, errno);
  buf.size = 0;
  buf.cap = cap;
  return buf;
}

static void delete_msg_buf(msg_buf_t buf)
{
  munmap(buf.buf, buf.cap);
}

static void extend_msg_buf(msg_buf_t *buf)
{
  buf->buf = mremap(buf->buf, buf->cap, buf->cap << 1, MREMAP_MAYMOVE);
  if (buf->buf == MAP_FAILED)
    INLINE_SYSCALL(exit, 1, errno);
  buf->cap <<= 1;
}

static void copy_to_buf(msg_buf_t *dst_buf, const void *src_buf, uint64_t size)
{
  if (dst_buf->cap < dst_buf->size + size)
    extend_msg_buf(dst_buf);
  memcpy(dst_buf->buf + dst_buf->size, src_buf, size);
  dst_buf->size += size;
}

static void copy_to_fd(int fd, msg_buf_t *src_buf)
{
  ssize_t wr_size = write(fd, src_buf->buf, src_buf->size);
  if (wr_size != src_buf->size)
    INLINE_SYSCALL(exit, 1, errno);
  src_buf->size = 0;
}

static void copy_from_fd(int fd, msg_buf_t *dst_buf, uint64_t size)
{
  while (dst_buf->cap < dst_buf->size + size)
    extend_msg_buf(dst_buf);
  ssize_t rd_total = 0;
  while (rd_total < size)
  {
    ssize_t rd_size = read(fd, dst_buf->buf + dst_buf->size, size - rd_total);
    if (rd_size == -1)
      INLINE_SYSCALL(exit, 1, errno);
    rd_total += rd_size;
    dst_buf->size += rd_size;
  }
}

void write_new_page(msg_buf_t *msg_buf, page_t *new_page)
{
  copy_to_buf(msg_buf, &new_page->address, sizeof(new_page->address));
  copy_to_buf(msg_buf, &new_page->runtime_revision, sizeof(new_page->runtime_revision));
  copy_to_buf(msg_buf, &new_page->client_revision, sizeof(new_page->client_revision));
  copy_to_buf(msg_buf, &new_page->size, sizeof(new_page->size));
  copy_to_buf(msg_buf, new_page->content, new_page->size);
}

uint64_t write_page_diff(msg_buf_t *msg_buf, const void *new_page, page_t *original_page, size_t size)
{
  typedef enum
  {
      UNCHANGED,
      CHANGED
  } check_state;
  check_state state = UNCHANGED;
  size_t change_start = 0;
  uint8_t *new_page_copy = alloca(size);
  memcpy(new_page_copy, new_page, size);
  const uint8_t *new_byte_ptr = (const uint8_t *)new_page_copy;
  uint8_t *original_byte_ptr = (uint8_t *)original_page->content;
  const uint64_t next_revision = original_page->client_revision + 1;
  uint64_t init_buf_pos = msg_buf->size;

  size_t offset = 0;
  if (original_page->stack_ptr)
    offset = original_page->stack_ptr + sizeof(void *) - original_page->address;
  while (offset < size)
  {
    if (*new_byte_ptr != *original_byte_ptr && state == UNCHANGED)
    {
      state = CHANGED;
      change_start = offset;
    }

    if (*new_byte_ptr == *original_byte_ptr && state == CHANGED)
    {
      state = UNCHANGED;
      const void *address = new_page + change_start;
      copy_to_buf(msg_buf, &address, sizeof(address));
      copy_to_buf(msg_buf, &original_page->runtime_revision, sizeof(original_page->runtime_revision));
      copy_to_buf(msg_buf, &next_revision, sizeof(next_revision));
      uint32_t content_size = offset - change_start;
      copy_to_buf(msg_buf, &content_size, sizeof(content_size));
      copy_to_buf(msg_buf, new_page_copy + change_start, content_size);
    }

    ++new_byte_ptr;
    ++original_byte_ptr;
    ++offset;
  }

  if (state == CHANGED)
  {
    const void *address = new_page + change_start;
    copy_to_buf(msg_buf, &address, sizeof(address));
    copy_to_buf(msg_buf, &original_page->runtime_revision, sizeof(original_page->runtime_revision));
    copy_to_buf(msg_buf, &next_revision, sizeof(next_revision));
    uint32_t content_size = offset - change_start;
    copy_to_buf(msg_buf, &content_size, sizeof(content_size));
    copy_to_buf(msg_buf, new_page_copy + change_start, content_size);
  }
  if (init_buf_pos != msg_buf->size)
  {
    memcpy(original_page->content, new_page_copy, size);
    return next_revision;
  }
  if (size == 0)
  {
    uint32_t content_size = size;
    const void *address = new_page + change_start;
    copy_to_buf(msg_buf, &address, sizeof(address));
    copy_to_buf(msg_buf, &original_page->runtime_revision, sizeof(original_page->runtime_revision));
    copy_to_buf(msg_buf, &next_revision, sizeof(next_revision));
    copy_to_buf(msg_buf, &content_size, sizeof(content_size));
  }
  return 0;
}

typedef struct mem_region_s {
  uint64_t start;
  uint64_t end;
  struct mem_region_s *prev;
  struct mem_region_s *next;
} mem_region_t;

typedef struct stack_region_s {
  mem_region_t *mem_region;
  __rtld_lock_define_recursive(, lock);
} stack_region_t;

static stack_region_t stack_region;

static int in_mem_region(mem_region_t *mem_region, uint64_t addr)
{
  return mem_region->start <= addr && addr < mem_region->end;
}

static void init_stack_region(void)
{
  stack_region.mem_region = malloc(sizeof(mem_region_t));
  if (!stack_region.mem_region)
    INLINE_SYSCALL(exit, 1, errno);
  struct rlimit limit;
  if (getrlimit(RLIMIT_STACK, &limit) == -1)
    INLINE_SYSCALL(exit, 1, errno);
  assert(limit.rlim_cur > 0x100000);
  uint64_t end = (uint64_t)__libc_stack_end;
  stack_region.mem_region->end = (end & 0xfffffffff000) + getpagesize();
  stack_region.mem_region->start = end - (limit.rlim_cur - 0x100000);
  stack_region.mem_region->prev = NULL;
  stack_region.mem_region->next = NULL;
  __rtld_lock_initialize(stack_region.lock);
}

static void add_stack_region(void *end)
{
  __rtld_lock_lock_recursive(stack_region.lock);
  mem_region_t *new_stack_region = malloc(sizeof(mem_region_t));
  if (!new_stack_region)
    INLINE_SYSCALL(exit, 1, errno);
  new_stack_region->prev = NULL;
  new_stack_region->next = stack_region.mem_region;
  stack_region.mem_region = new_stack_region;
  if (new_stack_region->next)
    new_stack_region->next->prev = new_stack_region;

  struct rlimit limit;
  if (getrlimit(RLIMIT_STACK, &limit) == -1)
    INLINE_SYSCALL(exit, 1, errno);
  uint64_t start = (uint64_t)end - limit.rlim_cur;
  new_stack_region->start = start;
  new_stack_region->end = (uint64_t)end;
  __rtld_lock_unlock_recursive(stack_region.lock);
}

static void delete_stack_region(uint64_t addr)
{
  __rtld_lock_lock_recursive(stack_region.lock);
  mem_region_t *stack_region_iter = stack_region.mem_region;
  while (stack_region_iter && !in_mem_region(stack_region_iter, addr))
    stack_region_iter = stack_region_iter->next;
  if (stack_region_iter)
  {
    if (stack_region_iter->prev)
      stack_region_iter->prev->next = stack_region_iter->next;
    else
      stack_region.mem_region = stack_region_iter->next;
    if (stack_region_iter->next)
      stack_region_iter->next->prev = stack_region_iter->prev;
    free(stack_region_iter);
  }
  __rtld_lock_unlock_recursive(stack_region.lock);
}

static uint64_t get_stack_bottom(uint64_t stack_ptr)
{
  uint64_t bottom = 0;
  __rtld_lock_lock_recursive(stack_region.lock);
  mem_region_t *stack_region_iter = stack_region.mem_region;
  while (stack_region_iter && !in_mem_region(stack_region_iter, stack_ptr))
    stack_region_iter = stack_region_iter->next;
  if (stack_region_iter)
    bottom = stack_region_iter->end;
  __rtld_lock_unlock_recursive(stack_region.lock);
  return bottom;
}

static uint64_t count_gnu_hash_symbol(struct link_map *map)
{
  uint64_t max_bucket = 0;
  for (size_t i = 0;i < map->l_nbuckets;i++)
  {
    Elf32_Word bucket = map->l_gnu_buckets[i];
    if (bucket > max_bucket)
      max_bucket = bucket;
  }
  uint64_t max_chain_idx = max_bucket;
  while (1)
  {
    const Elf32_Word *hasharr = &map->l_gnu_chain_zero[max_chain_idx];
    if (*hasharr & 1)
      break;
    max_chain_idx++;
  }
  return max_chain_idx + 1;
}

static unsigned long calc_loadlib_msg_size(struct link_map *map, const char *file)
{
  unsigned long msg_size = RPC_HEADER_SIZE + strlen(file) + /* null byte */ 1;
  const char *strtab = NULL;
  ElfW(Sym) *symtab = NULL;

  for (ElfW(Dyn) *dynobj = map->l_ld;dynobj->d_tag != DT_NULL;dynobj++)
  {
    switch (dynobj->d_tag)
    {
    case DT_STRTAB:
      strtab = (const char *)(dynobj->d_un.d_ptr);
      break;
    case DT_SYMTAB:
      symtab = (ElfW(Sym) *)(dynobj->d_un.d_ptr);
      break;
    }
  }
  uint64_t max_sym = count_gnu_hash_symbol(map);
  for (Elf_Symndx sym_cnt = 0;sym_cnt < max_sym;sym_cnt++)
  {
    switch (symtab->st_info)
    {
    case ELF64_ST_INFO(STB_GLOBAL, STT_FUNC):
    case ELF64_ST_INFO(STB_WEAK, STT_FUNC):
    case ELF64_ST_INFO(STB_GLOBAL, STT_GNU_IFUNC):
    case ELF64_ST_INFO(STB_WEAK, STT_GNU_IFUNC):
      if (symtab->st_size && symtab->st_other == ELF64_ST_VISIBILITY(STV_DEFAULT))
      {
        /* put function address */
        msg_size += sizeof(void *);
        /* put function name */
        msg_size += strlen(strtab + symtab->st_name) + /* null byte */ 1;
      }
    }
    symtab++;
  }
  return msg_size;
}

static void handle_loadlib(struct link_map *map, const char *file, int rpc_fd)
{
  char *strtab = NULL;
  ElfW(Sym) *symtab = NULL;
  void *func = NULL;
  int mprotect_size = getpagesize();
  const uint64_t page_mask = 0xfffffffffffff000;
  uint64_t bufsize = calc_loadlib_msg_size(map, file);
  uint64_t payload_size = bufsize - RPC_HEADER_SIZE;
  void *msg_buf = alloca(bufsize);
  void *msg_offset = msg_buf;
  rpc_msg_header_t header = {.msg_type = LOADLIB, .status = STATUS_OK, .client_id = getpid(), .payload_size = payload_size,};
  
  serialize_header(msg_buf, header);
  msg_offset += RPC_HEADER_SIZE;
  memcpy(msg_offset, file, strlen(file) + /* null byte */ 1);
  msg_offset += strlen(file) + /* null byte */ 1;

  for (ElfW(Dyn) *dynobj = map->l_ld;dynobj->d_tag != DT_NULL;dynobj++)
  {
    switch (dynobj->d_tag)
    {
    case DT_STRTAB:
      strtab = (char *)(dynobj->d_un.d_ptr);
      break;
    case DT_SYMTAB:
      symtab = (ElfW(Sym) *)(dynobj->d_un.d_ptr);
      break;
    }
  }

  uint64_t max_sym = count_gnu_hash_symbol(map);
  for (Elf_Symndx sym_cnt = 0;sym_cnt < max_sym;sym_cnt++)
  {
    switch (symtab->st_info)
    {
    case ELF64_ST_INFO(STB_GLOBAL, STT_FUNC):
    case ELF64_ST_INFO(STB_WEAK, STT_FUNC):
    case ELF64_ST_INFO(STB_GLOBAL, STT_GNU_IFUNC):
    case ELF64_ST_INFO(STB_WEAK, STT_GNU_IFUNC):
      if (symtab->st_size && symtab->st_other == ELF64_ST_VISIBILITY(STV_DEFAULT))
      {
        func = (void *)(map->l_addr + symtab->st_value);
        if (symtab->st_info == ELF64_ST_INFO(STB_GLOBAL, STT_GNU_IFUNC) ||\
            symtab->st_info == ELF64_ST_INFO(STB_WEAK, STT_GNU_IFUNC))
          func = (void *)((DL_FIXUP_VALUE_TYPE (*) (void)) (func)) ();
        /* put function address */
        memcpy(msg_offset, &func, sizeof(void *));
        msg_offset += sizeof(void *);

        /* put function name */
        memcpy(msg_offset, strtab + symtab->st_name,
          strlen(strtab + symtab->st_name) + /*null byte */ 1);
        msg_offset += strlen(strtab + symtab->st_name) + /* null byte */ 1;

        /* put sigill */
        void *page_start = (void *)((uint64_t)func & page_mask);
        if (mprotect(page_start, mprotect_size, PROT_READ | PROT_WRITE | PROT_EXEC))
          INLINE_SYSCALL(exit, 1, errno);
        
        *(uint8_t *)(func) = 0xd4;  /* #UD opcode */

        if (mprotect(page_start, mprotect_size, PROT_READ | PROT_EXEC))
          INLINE_SYSCALL(exit, 1, errno);
      }
    }
    symtab++;
  }

  /* send message */
  if (write(rpc_fd, msg_buf, bufsize) != bufsize)
    INLINE_SYSCALL(exit, 1, errno);

  if (read(rpc_fd, msg_buf, RPC_HEADER_SIZE) !=\
      RPC_HEADER_SIZE)
    INLINE_SYSCALL(exit, 1, errno);
  header = deserialize_header(msg_buf);
  if (header.msg_type != LOADLIB || header.status != STATUS_OK)
    INLINE_SYSCALL(exit, 1, header.status);

  close(rpc_fd);
}

static void handle_invokefunc(ucontext_t *ctx)
{
  const uint64_t page_mask = 0xfffffffffffff000;
  uint64_t prev_page_addr = 0;
  const int page_size = getpagesize();
  msg_buf_t msg_buf = make_msg_buf(page_size * 4);
  rpc_msg_header_t header = {0};
  page_t *new_page = NULL;
  uint64_t invokefunc_id;
  struct timespec start, end;
  lock_page_tbl();
  INLINE_SYSCALL(clock_gettime, 2, CLOCK_MONOTONIC, &start);
  uint64_t stack_bottom = get_stack_bottom(ctx->uc_mcontext.gregs[REG_RSP]);
  assert(stack_bottom);
  invokefunc_id = page_tbl.invokefunc_id++;
  copy_to_buf(&msg_buf, &header, RPC_HEADER_SIZE); /* seek buf */
  copy_to_buf(&msg_buf, &invokefunc_id, sizeof(invokefunc_id));
  copy_to_buf(&msg_buf, ctx->uc_mcontext.gregs, sizeof(gregset_t)); /* gregs */
  copy_to_buf(&msg_buf, ctx->uc_mcontext.fpregs, sizeof(struct _libc_fpstate)); /* x87/SSE */
  copy_to_buf(&msg_buf, &stack_bottom, sizeof(stack_bottom)); /* stack bottom */
  page_t *page = page_tbl.page_list;
  while (page)
  {
    uint64_t buf_size = msg_buf.size;
    uint64_t rev = 0;
page_check:
    if (page_exist((void *)page->address, page_size) == MAP_FAILED)
    {
      write_page_diff(&msg_buf, (void *)page->address, page, 0);
      page_t *tmp = page;
      page = page->next;
      delete_stack_region(tmp->address);
      remove_page(tmp->address);
      continue;
    }
    lock_curr_page();
    curr_page.curr_page = (void *)page->address;
    rev = write_page_diff(&msg_buf, (void *)page->address, page, page->size);
    // write(2, "write_page_diff\n", 16);
    if (!curr_page.curr_page)
    {
      munmap((void *)page->address, page->size);
      unlock_curr_page();
      msg_buf.size = buf_size;
      goto page_check;
    }
    unlock_curr_page();
    if (rev && rev != page->client_revision)
      page->client_revision++;
    page = page->next;
  }

  if (!get_page(ctx->uc_mcontext.gregs[REG_RSP]))
  {
    page_t *stack_page = malloc(sizeof(page_t));
    if (!stack_page)
      INLINE_SYSCALL(exit, 1, errno);
    stack_page->address = ctx->uc_mcontext.gregs[REG_RSP] & page_mask;
    stack_page->wr_addr = stack_page->address;
    stack_page->runtime_revision = 0;
    stack_page->client_revision = 0;
    stack_page->content = malloc(page_size);
    if (!stack_page->content)
      INLINE_SYSCALL(exit, 1, errno);
    stack_page->size = page_size;
    stack_page->successor_list = NULL;
    stack_page->prev = NULL;
    stack_page->next = NULL;
    memcpy(stack_page->content,
          (void *)(ctx->uc_mcontext.gregs[REG_RSP] & page_mask), page_size);
    add_page(stack_page);
    write_new_page(&msg_buf, stack_page);
  }
  page_t *stack_page = get_page(ctx->uc_mcontext.gregs[REG_RSP]);
  assert(stack_page);
  stack_page->stack_ptr = ctx->uc_mcontext.gregs[REG_RSP];
  unlock_page_tbl();
  header.msg_type = INVOKEFUNC;
  header.status = 0;
  header.client_id = getpid();
  header.payload_size = msg_buf.size - RPC_HEADER_SIZE;
  serialize_header(msg_buf.buf, header);

  INLINE_SYSCALL(clock_gettime, 2, CLOCK_MONOTONIC, &end);
  
  int rpc_fd = connect_rpc_sock();

send_message:
  copy_to_fd(rpc_fd, &msg_buf);

  copy_from_fd(rpc_fd, &msg_buf, RPC_HEADER_SIZE);
  header = deserialize_header(msg_buf.buf);
  copy_from_fd(rpc_fd, &msg_buf, header.payload_size);
  INLINE_SYSCALL(clock_gettime, 2, CLOCK_MONOTONIC, &start);
  if (header.msg_type != INVOKEFUNC)
    INLINE_SYSCALL(exit, 1, 0);
  if (header.status != STATUS_OK && header.status != STATUS_NOT_FOUND)
    INLINE_SYSCALL(exit, 1, header.status);
  
  uint64_t msg_offset = RPC_HEADER_SIZE +\
               sizeof(uint64_t) /* invokefunc_id */ +\
               sizeof(gregset_t) +\
               sizeof(struct _libc_fpstate) +\
               sizeof(uint64_t) /* stack_bottom */;
  while (msg_offset < msg_buf.size)
  {
    page_t page = {0};
    page.address = *(uint64_t *)(msg_buf.buf + msg_offset);
    msg_offset += sizeof(page.address);
    page.runtime_revision = *(uint64_t *)(msg_buf.buf + msg_offset);
    msg_offset += sizeof(page.runtime_revision);
    page.client_revision = *(uint64_t *)(msg_buf.buf + msg_offset);
    msg_offset += sizeof(page.client_revision);
    page.size = *(uint32_t *)(msg_buf.buf + msg_offset);
    if (header.status == STATUS_NOT_FOUND)
    {
      stack_bottom = 0;
      msg_buf.size = RPC_HEADER_SIZE +\
                   sizeof(uint64_t) /* invokefunc_id */ +\
                   sizeof(gregset_t) +\
                   sizeof(struct _libc_fpstate);
      page.size = page_size;
      new_page = malloc(sizeof(page_t));
      if (!new_page)
        INLINE_SYSCALL(exit, 1, errno);
      memcpy(new_page, &page, sizeof(page));
      new_page->content = malloc(page_size);
      if (!new_page->content)
        INLINE_SYSCALL(exit, 1, errno);
      lock_page_tbl();
      memcpy(new_page->content, (void *)new_page->address, new_page->size);
      new_page->wr_addr = new_page->address;
      add_page(new_page);
      unlock_page_tbl();
      copy_to_buf(&msg_buf, &stack_bottom, sizeof(stack_bottom));
      copy_to_buf(&msg_buf, &new_page->address, sizeof(new_page->address));
      copy_to_buf(&msg_buf, &new_page->runtime_revision, sizeof(new_page->runtime_revision));
      copy_to_buf(&msg_buf, &new_page->client_revision, sizeof(new_page->client_revision));
      copy_to_buf(&msg_buf, &new_page->size, sizeof(new_page->size));
      copy_to_buf(&msg_buf, new_page->content, new_page->size);
      header.status = STATUS_OK;
      header.payload_size = msg_buf.size - RPC_HEADER_SIZE;
      serialize_header(msg_buf.buf, header);
      goto send_message;
    }
    if (page.size == 0)
    {
      remove_page(page.address);
      continue;
    }
    lock_page_tbl();
    if (prev_page_addr && prev_page_addr != (page.address & page_mask))
    {
      page_t *prev_page = get_page(prev_page_addr);
      assert(prev_page);
      uint64_t rev = prev_page->runtime_revision++;
      notify_successor(prev_page->address, rev);
    }
    prev_page_addr = page.address & page_mask;
    msg_offset += sizeof(page.size);
    page.content = msg_buf.buf + msg_offset;
    msg_offset += page.size;
    page_t *wr_page = get_page(page.address);
    assert(wr_page);
    wait_prev_revision(page.address, page.runtime_revision);
    uint64_t min_offset = wr_page->stack_ptr + sizeof(void *) - wr_page->address;
    uint64_t offset = page.address - wr_page->address;
    memcpy((void *)(wr_page->content + offset), page.content, page.size);
    if (wr_page->stack_ptr && min_offset > offset && offset + page.size > min_offset)
    {
      page.size -= min_offset - offset;
      page.content += min_offset - offset;
      offset = min_offset;
    }
    else if (wr_page->stack_ptr && min_offset > offset)
      page.size = 0;
    if (page.size)
      memcpy((void *)(wr_page->wr_addr + offset), page.content, page.size);
    unlock_page_tbl();
  }
  close(rpc_fd);
  lock_page_tbl();
  if (prev_page_addr)
  {
    page_t *prev_page = get_page(prev_page_addr);
    if (prev_page)
    {
      uint64_t rev = prev_page->runtime_revision++;
      notify_successor(prev_page->address, rev);
    }
  }
  stack_page = get_page(ctx->uc_mcontext.gregs[REG_RSP]);
  assert(stack_page);
  stack_page->stack_ptr = 0;
  INLINE_SYSCALL(clock_gettime, 2, CLOCK_MONOTONIC, &end);
  unlock_page_tbl();
  memcpy(ctx->uc_mcontext.gregs,
          msg_buf.buf + RPC_HEADER_SIZE + sizeof(uint64_t),
          sizeof(gregset_t));
  memcpy(ctx->uc_mcontext.fpregs,
          msg_buf.buf + RPC_HEADER_SIZE + sizeof(uint64_t) + sizeof(gregset_t),
          sizeof(struct _libc_fpstate));
  delete_msg_buf(msg_buf);
  return;
}

static void restore_from_sigill(ucontext_t *ctx)
{
  asm volatile(
    "fxrstor (%%rax)"
    :
    : "a"(ctx->uc_mcontext.fpregs)
    :);
  asm volatile(
    "push %%rax\n\t"
    "popfq"
    :
    : "a"(ctx->uc_mcontext.gregs[REG_EFL])
    :);
  asm volatile(
    "mov %0, %%rsp"        
    :
    : "m"(ctx->uc_mcontext.gregs[REG_RSP])
    :);
#define SAVE_GREG(R)                         \
  asm volatile(                              \
    "push %%rax"                           \
    :                                      \
    : "a"(ctx->uc_mcontext.gregs[REG_##R]) \
    :)

  SAVE_GREG(RCX);
  SAVE_GREG(RAX);
  SAVE_GREG(RDX);
  SAVE_GREG(RBX);
  SAVE_GREG(RBP);
  SAVE_GREG(RSI);
  SAVE_GREG(RDI);
  SAVE_GREG(R8);
  SAVE_GREG(R9);
  SAVE_GREG(R10);
  SAVE_GREG(R11);
  SAVE_GREG(R12);
  SAVE_GREG(R13);
  SAVE_GREG(R14);
  SAVE_GREG(R15);
#undef SAVE_GREG
  asm volatile(
    "pop %r15\n\t"
    "pop %r14\n\t"
    "pop %r13\n\t"
    "pop %r12\n\t"
    "pop %r11\n\t"
    "pop %r10\n\t"
    "pop %r9\n\t"
    "pop %r8\n\t"
    "pop %rdi\n\t"
    "pop %rsi\n\t"
    "pop %rbp\n\t"
    "pop %rbx\n\t"
    "pop %rdx\n\t"
    "pop %rax\n\t"
    "pop %rcx\n\t"
    "ret"
  );
}

static void sigill_handler(int signal, siginfo_t *si, void *arg) {
	ucontext_t *ctx = arg;
  handle_invokefunc(ctx);
  restore_from_sigill(ctx);
}

static void restore_from_sigsegv(ucontext_t *ctx)
{
  asm volatile(
    "fxrstor (%%rax)"
    :
    : "a"(ctx->uc_mcontext.fpregs)
    :);
  asm volatile(
    "push %%rax\n\t"
    "popfq"
    :
    : "a"(ctx->uc_mcontext.gregs[REG_EFL])
    :);
  asm volatile(
    "mov %0, %%rsp"        
    :
    : "m"(ctx->uc_mcontext.gregs[REG_RSP])
    :);
  #define SAVE_GREG(R)                         \
  asm volatile(                              \
    "push %%rax"                           \
    :                                      \
    : "a"(ctx->uc_mcontext.gregs[REG_##R]) \
    :)
  SAVE_GREG(RIP);
  SAVE_GREG(RCX);
  SAVE_GREG(RAX);
  SAVE_GREG(RDX);
  SAVE_GREG(RBX);
  SAVE_GREG(RBP);
  SAVE_GREG(RSI);
  SAVE_GREG(RDI);
  SAVE_GREG(R8);
  SAVE_GREG(R9);
  SAVE_GREG(R10);
  SAVE_GREG(R11);
  SAVE_GREG(R12);
  SAVE_GREG(R13);
  SAVE_GREG(R14);
  SAVE_GREG(R15);
  #undef SAVE_GREG
  asm volatile(
    "pop %r15\n\t"
    "pop %r14\n\t"
    "pop %r13\n\t"
    "pop %r12\n\t"
    "pop %r11\n\t"
    "pop %r10\n\t"
    "pop %r9\n\t"
    "pop %r8\n\t"
    "pop %rdi\n\t"
    "pop %rsi\n\t"
    "pop %rbp\n\t"
    "pop %rbx\n\t"
    "pop %rdx\n\t"
    "pop %rax\n\t"
    "pop %rcx\n\t"
    "ret"
  );
}

static void sigsegv_handler(int signal, siginfo_t *si, void *arg)
{
  ucontext_t *ctx = arg;
  const uint64_t page_mask = 0xfffffffffffff000;
  if ((uint64_t)si->si_addr == ctx->uc_mcontext.gregs[REG_RIP])
    sigill_handler(signal, si, arg);
  if (((uint64_t)si->si_addr & page_mask) == (uint64_t)curr_page.curr_page)
  {
    void *mapped_addr = mmap(curr_page.curr_page, getpagesize(),
                              PROT_WRITE | PROT_READ,
                              MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (curr_page.curr_page != mapped_addr)
      INLINE_SYSCALL(exit, 1, errno);
    curr_page.curr_page = NULL;
    restore_from_sigsegv(ctx);
  }
  lock_page_tbl();
  if (get_page((uint64_t)si->si_addr))
  {
    wait_prev_revision((uint64_t)si->si_addr, 0);
    unlock_page_tbl();
    restore_from_sigsegv(ctx);
  }
  msg_buf_t msg_buf = make_msg_buf(getpagesize() << 1);
  rpc_msg_header_t header = {.msg_type = PULLPAGE, .status = STATUS_OK, .client_id = getpid(),};
  msg_buf.size = RPC_HEADER_SIZE;
  page_t *request_page = malloc(sizeof(page_t));
  if (!request_page)
    INLINE_SYSCALL(exit, 1, errno);
  memset(request_page, 0, sizeof(page_t));
  request_page->address = (uint64_t)si->si_addr & page_mask;
  add_page(request_page);
  unlock_page_tbl();
  copy_to_buf(&msg_buf, &request_page->address, sizeof(request_page->address));
  copy_to_buf(&msg_buf, &request_page->runtime_revision, sizeof(request_page->runtime_revision));
  copy_to_buf(&msg_buf, &request_page->client_revision, sizeof(request_page->client_revision));
  copy_to_buf(&msg_buf, &request_page->size, sizeof(request_page->size));
  header.payload_size = msg_buf.size;
  serialize_header(msg_buf.buf, header);
  int fd = connect_rpc_sock();
  copy_to_fd(fd, &msg_buf);
  copy_from_fd(fd, &msg_buf, RPC_HEADER_SIZE);
  header = deserialize_header(&msg_buf);
  copy_from_fd(fd, &msg_buf, header.payload_size);
  close(fd);
  lock_page_tbl();
  if (header.status != STATUS_OK)
    INLINE_SYSCALL(exit, 1, header.status);
  uint64_t msg_offset = RPC_HEADER_SIZE +\
                        sizeof(request_page->address) +\
                        sizeof(request_page->runtime_revision) +\
                        sizeof(request_page->client_revision);
  request_page->size = *(uint32_t *)(msg_buf.buf + msg_offset);
  msg_offset += sizeof(request_page->size);
  request_page->content = malloc(request_page->size);
  if (!request_page->content)
    INLINE_SYSCALL(exit, 1, errno);
  memcpy(request_page->content, msg_buf.buf + msg_offset, request_page->size);
  int memfd = memfd_create("", MFD_CLOEXEC);
  if (memfd == -1)
    INLINE_SYSCALL(exit, 1, errno);
  if (ftruncate(memfd, request_page->size) == -1)
    INLINE_SYSCALL(exit, 1, errno);
  void *wr_addr = mmap(NULL, request_page->size,
                       PROT_READ | PROT_WRITE,
                       MAP_SHARED, memfd, 0);
  if (wr_addr == MAP_FAILED)
    INLINE_SYSCALL(exit, 1, errno);
  memcpy(wr_addr, request_page->content, request_page->size);
  request_page->wr_addr = (uint64_t)wr_addr;
  void *mapped_addr = mmap((void *)request_page->address,
                            request_page->size, PROT_READ | PROT_WRITE,
                            MAP_SHARED, memfd, 0);
  if (mapped_addr != (void *)request_page->address)
    INLINE_SYSCALL(exit, 1, errno);
  close(memfd);
  delete_msg_buf(msg_buf);
  notify_successor(request_page->address, 0);
  unlock_page_tbl();
  restore_from_sigsegv(ctx);
}

static void
dl_main (const ElfW(Phdr) *phdr,
	 ElfW(Word) phnum,
	 ElfW(Addr) *user_entry,
	 ElfW(auxv_t) *auxv)
{
  struct link_map *main_map;
  size_t file_size;
  char *file;
  unsigned int i;
  bool rtld_is_main = false;
  void *tcbp = NULL;

  struct dl_main_state state;
  dl_main_state_init (&state);

  __tls_pre_init_tp ();

#if !PTHREAD_IN_LIBC
  /* The explicit initialization here is cheaper than processing the reloc
     in the _rtld_local definition's initializer.  */
  GL(dl_make_stack_executable_hook) = &_dl_make_stack_executable;
#endif

  /* Process the environment variable which control the behaviour.  */
  process_envvars (&state);

#ifndef HAVE_INLINED_SYSCALLS
  /* Set up a flag which tells we are just starting.  */
  _dl_starting_up = 1;
#endif

  const char *ld_so_name = _dl_argv[0];
  if (*user_entry == (ElfW(Addr)) ENTRY_POINT)
    {
      /* Ho ho.  We are not the program interpreter!  We are the program
	 itself!  This means someone ran ld.so as a command.  Well, that
	 might be convenient to do sometimes.  We support it by
	 interpreting the args like this:

	 ld.so PROGRAM ARGS...

	 The first argument is the name of a file containing an ELF
	 executable we will load and run with the following arguments.
	 To simplify life here, PROGRAM is searched for using the
	 normal rules for shared objects, rather than $PATH or anything
	 like that.  We just load it and use its entry point; we don't
	 pay attention to its PT_INTERP command (we are the interpreter
	 ourselves).  This is an easy way to test a new ld.so before
	 installing it.  */
      rtld_is_main = true;

      char *argv0 = NULL;
      char **orig_argv = _dl_argv;

      /* Note the place where the dynamic linker actually came from.  */
      GL(dl_rtld_map).l_name = rtld_progname;

      while (_dl_argc > 1)
	if (! strcmp (_dl_argv[1], "--list"))
	  {
	    if (state.mode != rtld_mode_help)
	      {
	       state.mode = rtld_mode_list;
		/* This means do no dependency analysis.  */
		GLRO(dl_lazy) = -1;
	      }

	    --_dl_argc;
	    ++_dl_argv;
	  }
	else if (! strcmp (_dl_argv[1], "--verify"))
	  {
	    if (state.mode != rtld_mode_help)
	      state.mode = rtld_mode_verify;

	    --_dl_argc;
	    ++_dl_argv;
	  }
	else if (! strcmp (_dl_argv[1], "--inhibit-cache"))
	  {
	    GLRO(dl_inhibit_cache) = 1;
	    --_dl_argc;
	    ++_dl_argv;
	  }
	else if (! strcmp (_dl_argv[1], "--library-path")
		 && _dl_argc > 2)
	  {
	    state.library_path = _dl_argv[2];
	    state.library_path_source = "--library-path";

	    _dl_argc -= 2;
	    _dl_argv += 2;
	  }
	else if (! strcmp (_dl_argv[1], "--inhibit-rpath")
		 && _dl_argc > 2)
	  {
	    GLRO(dl_inhibit_rpath) = _dl_argv[2];

	    _dl_argc -= 2;
	    _dl_argv += 2;
	  }
	else if (! strcmp (_dl_argv[1], "--audit") && _dl_argc > 2)
	  {
	    audit_list_add_string (&state.audit_list, _dl_argv[2]);

	    _dl_argc -= 2;
	    _dl_argv += 2;
	  }
	else if (! strcmp (_dl_argv[1], "--preload") && _dl_argc > 2)
	  {
	    state.preloadarg = _dl_argv[2];
	    _dl_argc -= 2;
	    _dl_argv += 2;
	  }
	else if (! strcmp (_dl_argv[1], "--argv0") && _dl_argc > 2)
	  {
	    argv0 = _dl_argv[2];

	    _dl_argc -= 2;
	    _dl_argv += 2;
	  }
	else if (strcmp (_dl_argv[1], "--glibc-hwcaps-prepend") == 0
		 && _dl_argc > 2)
	  {
	    state.glibc_hwcaps_prepend = _dl_argv[2];
	    _dl_argc -= 2;
	    _dl_argv += 2;
	  }
	else if (strcmp (_dl_argv[1], "--glibc-hwcaps-mask") == 0
		 && _dl_argc > 2)
	  {
	    state.glibc_hwcaps_mask = _dl_argv[2];
	    _dl_argc -= 2;
	    _dl_argv += 2;
	  }
#if HAVE_TUNABLES
	else if (! strcmp (_dl_argv[1], "--list-tunables"))
	  {
	    state.mode = rtld_mode_list_tunables;

	    --_dl_argc;
	    ++_dl_argv;
	  }
#endif
	else if (! strcmp (_dl_argv[1], "--list-diagnostics"))
	  {
	    state.mode = rtld_mode_list_diagnostics;

	    --_dl_argc;
	    ++_dl_argv;
	  }
	else if (strcmp (_dl_argv[1], "--help") == 0)
	  {
	    state.mode = rtld_mode_help;
	    --_dl_argc;
	    ++_dl_argv;
	  }
	else if (strcmp (_dl_argv[1], "--version") == 0)
	  _dl_version ();
	else if (_dl_argv[1][0] == '-' && _dl_argv[1][1] == '-')
	  {
	   if (_dl_argv[1][1] == '\0')
	     /* End of option list.  */
	     break;
	   else
	     /* Unrecognized option.  */
	     _dl_usage (ld_so_name, _dl_argv[1]);
	  }
	else
	  break;

#if HAVE_TUNABLES
      if (__glibc_unlikely (state.mode == rtld_mode_list_tunables))
	{
	  __tunables_print ();
	  _exit (0);
	}
#endif

      if (state.mode == rtld_mode_list_diagnostics)
	_dl_print_diagnostics (_environ);

      /* If we have no further argument the program was called incorrectly.
	 Grant the user some education.  */
      if (_dl_argc < 2)
	{
	  if (state.mode == rtld_mode_help)
	    /* --help without an executable is not an error.  */
	    _dl_help (ld_so_name, &state);
	  else
	    _dl_usage (ld_so_name, NULL);
	}

      --_dl_argc;
      ++_dl_argv;

      /* The initialization of _dl_stack_flags done below assumes the
	 executable's PT_GNU_STACK may have been honored by the kernel, and
	 so a PT_GNU_STACK with PF_X set means the stack started out with
	 execute permission.  However, this is not really true if the
	 dynamic linker is the executable the kernel loaded.  For this
	 case, we must reinitialize _dl_stack_flags to match the dynamic
	 linker itself.  If the dynamic linker was built with a
	 PT_GNU_STACK, then the kernel may have loaded us with a
	 nonexecutable stack that we will have to make executable when we
	 load the program below unless it has a PT_GNU_STACK indicating
	 nonexecutable stack is ok.  */

      for (const ElfW(Phdr) *ph = phdr; ph < &phdr[phnum]; ++ph)
	if (ph->p_type == PT_GNU_STACK)
	  {
	    GL(dl_stack_flags) = ph->p_flags;
	    break;
	  }

      if (__glibc_unlikely (state.mode == rtld_mode_verify
			    || state.mode == rtld_mode_help))
	{
	  const char *objname;
	  const char *err_str = NULL;
	  struct map_args args;
	  bool malloced;

	  args.str = rtld_progname;
	  args.loader = NULL;
	  args.mode = __RTLD_OPENEXEC;
	  (void) _dl_catch_error (&objname, &err_str, &malloced, map_doit,
				  &args);
	  if (__glibc_unlikely (err_str != NULL))
	    {
	      /* We don't free the returned string, the programs stops
		 anyway.  */
	      if (state.mode == rtld_mode_help)
		/* Mask the failure to load the main object.  The help
		   message contains less information in this case.  */
		_dl_help (ld_so_name, &state);
	      else
		_exit (EXIT_FAILURE);
	    }
	}
      else
	{
	  RTLD_TIMING_VAR (start);
	  rtld_timer_start (&start);
	  _dl_map_object (NULL, rtld_progname, lt_executable, 0,
			  __RTLD_OPENEXEC, LM_ID_BASE);
	  rtld_timer_stop (&load_time, start);
	}

      /* Now the map for the main executable is available.  */
      main_map = GL(dl_ns)[LM_ID_BASE]._ns_loaded;

      if (__glibc_likely (state.mode == rtld_mode_normal))
	rtld_chain_load (main_map, argv0);

      phdr = main_map->l_phdr;
      phnum = main_map->l_phnum;
      /* We overwrite here a pointer to a malloc()ed string.  But since
	 the malloc() implementation used at this point is the dummy
	 implementations which has no real free() function it does not
	 makes sense to free the old string first.  */
      main_map->l_name = (char *) "";
      *user_entry = main_map->l_entry;

      /* Set bit indicating this is the main program map.  */
      main_map->l_main_map = 1;

#ifdef HAVE_AUX_VECTOR
      /* Adjust the on-stack auxiliary vector so that it looks like the
	 binary was executed directly.  */
      for (ElfW(auxv_t) *av = auxv; av->a_type != AT_NULL; av++)
	switch (av->a_type)
	  {
	  case AT_PHDR:
	    av->a_un.a_val = (uintptr_t) phdr;
	    break;
	  case AT_PHNUM:
	    av->a_un.a_val = phnum;
	    break;
	  case AT_ENTRY:
	    av->a_un.a_val = *user_entry;
	    break;
	  case AT_EXECFN:
	    av->a_un.a_val = (uintptr_t) _dl_argv[0];
	    break;
	  }
#endif

      /* Set the argv[0] string now that we've processed the executable.  */
      if (argv0 != NULL)
        _dl_argv[0] = argv0;

      /* Adjust arguments for the application entry point.  */
      _dl_start_args_adjust (_dl_argv - orig_argv);
    }
  else
    {
      /* Create a link_map for the executable itself.
	 This will be what dlopen on "" returns.  */
      main_map = _dl_new_object ((char *) "", "", lt_executable, NULL,
				 __RTLD_OPENEXEC, LM_ID_BASE);
      assert (main_map != NULL);
      main_map->l_phdr = phdr;
      main_map->l_phnum = phnum;
      main_map->l_entry = *user_entry;

      /* Even though the link map is not yet fully initialized we can add
	 it to the map list since there are no possible users running yet.  */
      _dl_add_to_namespace_list (main_map, LM_ID_BASE);
      assert (main_map == GL(dl_ns)[LM_ID_BASE]._ns_loaded);

      /* At this point we are in a bit of trouble.  We would have to
	 fill in the values for l_dev and l_ino.  But in general we
	 do not know where the file is.  We also do not handle AT_EXECFD
	 even if it would be passed up.

	 We leave the values here defined to 0.  This is normally no
	 problem as the program code itself is normally no shared
	 object and therefore cannot be loaded dynamically.  Nothing
	 prevent the use of dynamic binaries and in these situations
	 we might get problems.  We might not be able to find out
	 whether the object is already loaded.  But since there is no
	 easy way out and because the dynamic binary must also not
	 have an SONAME we ignore this program for now.  If it becomes
	 a problem we can force people using SONAMEs.  */

      /* We delay initializing the path structure until we got the dynamic
	 information for the program.  */
    }

  bool has_interp = rtld_setup_main_map (main_map);

  /* If the current libname is different from the SONAME, add the
     latter as well.  */
  if (GL(dl_rtld_map).l_info[DT_SONAME] != NULL
      && strcmp (GL(dl_rtld_map).l_libname->name,
		 (const char *) D_PTR (&GL(dl_rtld_map), l_info[DT_STRTAB])
		 + GL(dl_rtld_map).l_info[DT_SONAME]->d_un.d_val) != 0)
    {
      static struct libname_list newname;
      newname.name = ((char *) D_PTR (&GL(dl_rtld_map), l_info[DT_STRTAB])
		      + GL(dl_rtld_map).l_info[DT_SONAME]->d_un.d_ptr);
      newname.next = NULL;
      newname.dont_free = 1;

      assert (GL(dl_rtld_map).l_libname->next == NULL);
      GL(dl_rtld_map).l_libname->next = &newname;
    }
  /* The ld.so must be relocated since otherwise loading audit modules
     will fail since they reuse the very same ld.so.  */
  assert (GL(dl_rtld_map).l_relocated);

  if (! rtld_is_main)
    {
      /* Extract the contents of the dynamic section for easy access.  */
      elf_get_dynamic_info (main_map, false, false);

      /* If the main map is libc.so, update the base namespace to
	 refer to this map.  If libc.so is loaded later, this happens
	 in _dl_map_object_from_fd.  */
      if (main_map->l_info[DT_SONAME] != NULL
	  && (strcmp (((const char *) D_PTR (main_map, l_info[DT_STRTAB])
		      + main_map->l_info[DT_SONAME]->d_un.d_val), LIBC_SO)
	      == 0))
	GL(dl_ns)[LM_ID_BASE].libc_map = main_map;

      /* Set up our cache of pointers into the hash table.  */
      _dl_setup_hash (main_map);
    }

  if (__glibc_unlikely (state.mode == rtld_mode_verify))
    {
      /* We were called just to verify that this is a dynamic
	 executable using us as the program interpreter.  Exit with an
	 error if we were not able to load the binary or no interpreter
	 is specified (i.e., this is no dynamically linked binary.  */
      if (main_map->l_ld == NULL)
	_exit (1);

      _exit (has_interp ? 0 : 2);
    }

  struct link_map **first_preload = &GL(dl_rtld_map).l_next;
  /* Set up the data structures for the system-supplied DSO early,
     so they can influence _dl_init_paths.  */
  setup_vdso (main_map, &first_preload);

  /* With vDSO setup we can initialize the function pointers.  */
  setup_vdso_pointers ();

  /* Initialize the data structures for the search paths for shared
     objects.  */
  call_init_paths (&state);

  /* Initialize _r_debug_extended.  */
  struct r_debug *r = _dl_debug_initialize (GL(dl_rtld_map).l_addr,
					    LM_ID_BASE);
  r->r_state = RT_CONSISTENT;

  /* Put the link_map for ourselves on the chain so it can be found by
     name.  Note that at this point the global chain of link maps contains
     exactly one element, which is pointed to by dl_loaded.  */
  if (! GL(dl_rtld_map).l_name)
    /* If not invoked directly, the dynamic linker shared object file was
       found by the PT_INTERP name.  */
    GL(dl_rtld_map).l_name = (char *) GL(dl_rtld_map).l_libname->name;
  GL(dl_rtld_map).l_type = lt_library;
  main_map->l_next = &GL(dl_rtld_map);
  GL(dl_rtld_map).l_prev = main_map;
  ++GL(dl_ns)[LM_ID_BASE]._ns_nloaded;
  ++GL(dl_load_adds);

  /* Starting from binutils-2.23, the linker will define the magic symbol
     __ehdr_start to point to our own ELF header if it is visible in a
     segment that also includes the phdrs.  If that's not available, we use
     the old method that assumes the beginning of the file is part of the
     lowest-addressed PT_LOAD segment.  */

  /* Set up the program header information for the dynamic linker
     itself.  It is needed in the dl_iterate_phdr callbacks.  */
  const ElfW(Ehdr) *rtld_ehdr = &__ehdr_start;
  assert (rtld_ehdr->e_ehsize == sizeof *rtld_ehdr);
  assert (rtld_ehdr->e_phentsize == sizeof (ElfW(Phdr)));

  const ElfW(Phdr) *rtld_phdr = (const void *) rtld_ehdr + rtld_ehdr->e_phoff;

  GL(dl_rtld_map).l_phdr = rtld_phdr;
  GL(dl_rtld_map).l_phnum = rtld_ehdr->e_phnum;


  /* PT_GNU_RELRO is usually the last phdr.  */
  size_t cnt = rtld_ehdr->e_phnum;
  while (cnt-- > 0)
    if (rtld_phdr[cnt].p_type == PT_GNU_RELRO)
      {
	GL(dl_rtld_map).l_relro_addr = rtld_phdr[cnt].p_vaddr;
	GL(dl_rtld_map).l_relro_size = rtld_phdr[cnt].p_memsz;
	break;
      }

  /* Add the dynamic linker to the TLS list if it also uses TLS.  */
  if (GL(dl_rtld_map).l_tls_blocksize != 0)
    /* Assign a module ID.  Do this before loading any audit modules.  */
    _dl_assign_tls_modid (&GL(dl_rtld_map));

  audit_list_add_dynamic_tag (&state.audit_list, main_map, DT_AUDIT);
  audit_list_add_dynamic_tag (&state.audit_list, main_map, DT_DEPAUDIT);

  /* At this point, all data has been obtained that is included in the
     --help output.  */
  if (__glibc_unlikely (state.mode == rtld_mode_help))
    _dl_help (ld_so_name, &state);

  /* If we have auditing DSOs to load, do it now.  */
  bool need_security_init = true;
  if (state.audit_list.length > 0)
    {
      size_t naudit = audit_list_count (&state.audit_list);

      /* Since we start using the auditing DSOs right away we need to
	 initialize the data structures now.  */
      tcbp = init_tls (naudit);

      /* Initialize security features.  We need to do it this early
	 since otherwise the constructors of the audit libraries will
	 use different values (especially the pointer guard) and will
	 fail later on.  */
      security_init ();
      need_security_init = false;

      load_audit_modules (main_map, &state.audit_list);

      /* The count based on audit strings may overestimate the number
	 of audit modules that got loaded, but not underestimate.  */
      assert (GLRO(dl_naudit) <= naudit);
    }

  /* Keep track of the currently loaded modules to count how many
     non-audit modules which use TLS are loaded.  */
  size_t count_modids = _dl_count_modids ();

  /* Set up debugging before the debugger is notified for the first time.  */
  elf_setup_debug_entry (main_map, r);

  /* We start adding objects.  */
  r->r_state = RT_ADD;
  _dl_debug_state ();
  LIBC_PROBE (init_start, 2, LM_ID_BASE, r);

  /* Auditing checkpoint: we are ready to signal that the initial map
     is being constructed.  */
  _dl_audit_activity_map (main_map, LA_ACT_ADD);

  /* We have two ways to specify objects to preload: via environment
     variable and via the file /etc/ld.so.preload.  The latter can also
     be used when security is enabled.  */
  assert (*first_preload == NULL);
  struct link_map **preloads = NULL;
  unsigned int npreloads = 0;

  if (__glibc_unlikely (state.preloadlist != NULL))
    {
      RTLD_TIMING_VAR (start);
      rtld_timer_start (&start);
      npreloads += handle_preload_list (state.preloadlist, main_map,
					"LD_PRELOAD");
      rtld_timer_accum (&load_time, start);
    }

  if (__glibc_unlikely (state.preloadarg != NULL))
    {
      RTLD_TIMING_VAR (start);
      rtld_timer_start (&start);
      npreloads += handle_preload_list (state.preloadarg, main_map,
					"--preload");
      rtld_timer_accum (&load_time, start);
    }

  /* There usually is no ld.so.preload file, it should only be used
     for emergencies and testing.  So the open call etc should usually
     fail.  Using access() on a non-existing file is faster than using
     open().  So we do this first.  If it succeeds we do almost twice
     the work but this does not matter, since it is not for production
     use.  */
  static const char preload_file[] = "/etc/ld.so.preload";
  if (__glibc_unlikely (__access (preload_file, R_OK) == 0))
    {
      /* Read the contents of the file.  */
      file = _dl_sysdep_read_whole_file (preload_file, &file_size,
					 PROT_READ | PROT_WRITE);
      if (__glibc_unlikely (file != MAP_FAILED))
	{
	  /* Parse the file.  It contains names of libraries to be loaded,
	     separated by white spaces or `:'.  It may also contain
	     comments introduced by `#'.  */
	  char *problem;
	  char *runp;
	  size_t rest;

	  /* Eliminate comments.  */
	  runp = file;
	  rest = file_size;
	  while (rest > 0)
	    {
	      char *comment = memchr (runp, '#', rest);
	      if (comment == NULL)
		break;

	      rest -= comment - runp;
	      do
		*comment = ' ';
	      while (--rest > 0 && *++comment != '\n');
	    }

	  /* We have one problematic case: if we have a name at the end of
	     the file without a trailing terminating characters, we cannot
	     place the \0.  Handle the case separately.  */
	  if (file[file_size - 1] != ' ' && file[file_size - 1] != '\t'
	      && file[file_size - 1] != '\n' && file[file_size - 1] != ':')
	    {
	      problem = &file[file_size];
	      while (problem > file && problem[-1] != ' '
		     && problem[-1] != '\t'
		     && problem[-1] != '\n' && problem[-1] != ':')
		--problem;

	      if (problem > file)
		problem[-1] = '\0';
	    }
	  else
	    {
	      problem = NULL;
	      file[file_size - 1] = '\0';
	    }

	  RTLD_TIMING_VAR (start);
	  rtld_timer_start (&start);

	  if (file != problem)
	    {
	      char *p;
	      runp = file;
	      while ((p = strsep (&runp, ": \t\n")) != NULL)
		if (p[0] != '\0')
		  npreloads += do_preload (p, main_map, preload_file);
	    }

	  if (problem != NULL)
	    {
	      char *p = strndupa (problem, file_size - (problem - file));

	      npreloads += do_preload (p, main_map, preload_file);
	    }

	  rtld_timer_accum (&load_time, start);

	  /* We don't need the file anymore.  */
	  __munmap (file, file_size);
	}
    }

  if (__glibc_unlikely (*first_preload != NULL))
    {
      /* Set up PRELOADS with a vector of the preloaded libraries.  */
      struct link_map *l = *first_preload;
      preloads = __alloca (npreloads * sizeof preloads[0]);
      i = 0;
      do
	{
	  preloads[i++] = l;
	  l = l->l_next;
	} while (l);
      assert (i == npreloads);
    }

#ifdef NEED_DL_SYSINFO_DSO
  /* Now that the audit modules are opened, call la_objopen for the vDSO.  */
  if (GLRO(dl_sysinfo_map) != NULL)
    _dl_audit_objopen (GLRO(dl_sysinfo_map), LM_ID_BASE);
#endif

  /* Load all the libraries specified by DT_NEEDED entries.  If LD_PRELOAD
     specified some libraries to load, these are inserted before the actual
     dependencies in the executable's searchlist for symbol resolution.  */
  {
    RTLD_TIMING_VAR (start);
    rtld_timer_start (&start);
    _dl_map_object_deps (main_map, preloads, npreloads,
			 state.mode == rtld_mode_trace, 0);
    rtld_timer_accum (&load_time, start);
  }

  /* Mark all objects as being in the global scope.  */
  for (i = main_map->l_searchlist.r_nlist; i > 0; )
    main_map->l_searchlist.r_list[--i]->l_global = 1;

  /* Remove _dl_rtld_map from the chain.  */
  GL(dl_rtld_map).l_prev->l_next = GL(dl_rtld_map).l_next;
  if (GL(dl_rtld_map).l_next != NULL)
    GL(dl_rtld_map).l_next->l_prev = GL(dl_rtld_map).l_prev;

  for (i = 1; i < main_map->l_searchlist.r_nlist; ++i)
    if (main_map->l_searchlist.r_list[i] == &GL(dl_rtld_map))
      break;

  bool rtld_multiple_ref = false;
  if (__glibc_likely (i < main_map->l_searchlist.r_nlist))
    {
      /* Some DT_NEEDED entry referred to the interpreter object itself, so
	 put it back in the list of visible objects.  We insert it into the
	 chain in symbol search order because gdb uses the chain's order as
	 its symbol search order.  */
      rtld_multiple_ref = true;

      GL(dl_rtld_map).l_prev = main_map->l_searchlist.r_list[i - 1];
      if (__glibc_likely (state.mode == rtld_mode_normal))
	{
	  GL(dl_rtld_map).l_next = (i + 1 < main_map->l_searchlist.r_nlist
				    ? main_map->l_searchlist.r_list[i + 1]
				    : NULL);
#ifdef NEED_DL_SYSINFO_DSO
	  if (GLRO(dl_sysinfo_map) != NULL
	      && GL(dl_rtld_map).l_prev->l_next == GLRO(dl_sysinfo_map)
	      && GL(dl_rtld_map).l_next != GLRO(dl_sysinfo_map))
	    GL(dl_rtld_map).l_prev = GLRO(dl_sysinfo_map);
#endif
	}
      else
	/* In trace mode there might be an invisible object (which we
	   could not find) after the previous one in the search list.
	   In this case it doesn't matter much where we put the
	   interpreter object, so we just initialize the list pointer so
	   that the assertion below holds.  */
	GL(dl_rtld_map).l_next = GL(dl_rtld_map).l_prev->l_next;

      assert (GL(dl_rtld_map).l_prev->l_next == GL(dl_rtld_map).l_next);
      GL(dl_rtld_map).l_prev->l_next = &GL(dl_rtld_map);
      if (GL(dl_rtld_map).l_next != NULL)
	{
	  assert (GL(dl_rtld_map).l_next->l_prev == GL(dl_rtld_map).l_prev);
	  GL(dl_rtld_map).l_next->l_prev = &GL(dl_rtld_map);
	}
    }

  /* Now let us see whether all libraries are available in the
     versions we need.  */
  {
    struct version_check_args args;
    args.doexit = state.mode == rtld_mode_normal;
    args.dotrace = state.mode == rtld_mode_trace;
    _dl_receive_error (print_missing_version, version_check_doit, &args);
  }

  /* We do not initialize any of the TLS functionality unless any of the
     initial modules uses TLS.  This makes dynamic loading of modules with
     TLS impossible, but to support it requires either eagerly doing setup
     now or lazily doing it later.  Doing it now makes us incompatible with
     an old kernel that can't perform TLS_INIT_TP, even if no TLS is ever
     used.  Trying to do it lazily is too hairy to try when there could be
     multiple threads (from a non-TLS-using libpthread).  */
  bool was_tls_init_tp_called = tls_init_tp_called;
  if (tcbp == NULL)
    tcbp = init_tls (0);

  if (__glibc_likely (need_security_init))
    /* Initialize security features.  But only if we have not done it
       earlier.  */
    security_init ();

  if (__glibc_unlikely (state.mode != rtld_mode_normal))
    {
      /* We were run just to list the shared libraries.  It is
	 important that we do this before real relocation, because the
	 functions we call below for output may no longer work properly
	 after relocation.  */
      struct link_map *l;

      if (GLRO(dl_debug_mask) & DL_DEBUG_UNUSED)
	{
	  /* Look through the dependencies of the main executable
	     and determine which of them is not actually
	     required.  */
	  struct link_map *l = main_map;

	  /* Relocate the main executable.  */
	  struct relocate_args args = { .l = l,
					.reloc_mode = ((GLRO(dl_lazy)
						       ? RTLD_LAZY : 0)
						       | __RTLD_NOIFUNC) };
	  _dl_receive_error (print_unresolved, relocate_doit, &args);

	  /* This loop depends on the dependencies of the executable to
	     correspond in number and order to the DT_NEEDED entries.  */
	  ElfW(Dyn) *dyn = main_map->l_ld;
	  bool first = true;
	  while (dyn->d_tag != DT_NULL)
	    {
	      if (dyn->d_tag == DT_NEEDED)
		{
		  l = l->l_next;
#ifdef NEED_DL_SYSINFO_DSO
		  /* Skip the VDSO since it's not part of the list
		     of objects we brought in via DT_NEEDED entries.  */
		  if (l == GLRO(dl_sysinfo_map))
		    l = l->l_next;
#endif
		  if (!l->l_used)
		    {
		      if (first)
			{
			  _dl_printf ("Unused direct dependencies:\n");
			  first = false;
			}

		      _dl_printf ("\t%s\n", l->l_name);
		    }
		}

	      ++dyn;
	    }

	  _exit (first != true);
	}
      else if (! main_map->l_info[DT_NEEDED])
	_dl_printf ("\tstatically linked\n");
      else
	{
	  for (l = state.mode_trace_program ? main_map : main_map->l_next;
	       l; l = l->l_next) {
	    if (l->l_faked)
	      /* The library was not found.  */
	      _dl_printf ("\t%s => not found\n",  l->l_libname->name);
	    else
	      _dl_printf ("\t%s => %s (0x%0*Zx)\n",
			  DSO_FILENAME (l->l_libname->name),
			  DSO_FILENAME (l->l_name),
			  (int) sizeof l->l_map_start * 2,
			  (size_t) l->l_map_start);
	  }
	}

      if (__glibc_unlikely (state.mode != rtld_mode_trace))
	for (i = 1; i < (unsigned int) _dl_argc; ++i)
	  {
	    const ElfW(Sym) *ref = NULL;
	    ElfW(Addr) loadbase;
	    lookup_t result;

	    result = _dl_lookup_symbol_x (_dl_argv[i], main_map,
					  &ref, main_map->l_scope,
					  NULL, ELF_RTYPE_CLASS_PLT,
					  DL_LOOKUP_ADD_DEPENDENCY, NULL);

	    loadbase = LOOKUP_VALUE_ADDRESS (result, false);

	    _dl_printf ("%s found at 0x%0*Zd in object at 0x%0*Zd\n",
			_dl_argv[i],
			(int) sizeof ref->st_value * 2,
			(size_t) ref->st_value,
			(int) sizeof loadbase * 2, (size_t) loadbase);
	  }
      else
	{
	  /* If LD_WARN is set, warn about undefined symbols.  */
	  if (GLRO(dl_lazy) >= 0 && GLRO(dl_verbose))
	    {
	      /* We have to do symbol dependency testing.  */
	      struct relocate_args args;
	      unsigned int i;

	      args.reloc_mode = ((GLRO(dl_lazy) ? RTLD_LAZY : 0)
				 | __RTLD_NOIFUNC);

	      i = main_map->l_searchlist.r_nlist;
	      while (i-- > 0)
		{
		  struct link_map *l = main_map->l_initfini[i];
		  if (l != &GL(dl_rtld_map) && ! l->l_faked)
		    {
		      args.l = l;
		      _dl_receive_error (print_unresolved, relocate_doit,
					 &args);
		    }
		}

	    }
#define VERNEEDTAG (DT_NUM + DT_THISPROCNUM + DT_VERSIONTAGIDX (DT_VERNEED))
	  if (state.version_info)
	    {
	      /* Print more information.  This means here, print information
		 about the versions needed.  */
	      int first = 1;
	      struct link_map *map;

	      for (map = main_map; map != NULL; map = map->l_next)
		{
		  const char *strtab;
		  ElfW(Dyn) *dyn = map->l_info[VERNEEDTAG];
		  ElfW(Verneed) *ent;

		  if (dyn == NULL)
		    continue;

		  strtab = (const void *) D_PTR (map, l_info[DT_STRTAB]);
		  ent = (ElfW(Verneed) *) (map->l_addr + dyn->d_un.d_ptr);

		  if (first)
		    {
		      _dl_printf ("\n\tVersion information:\n");
		      first = 0;
		    }

		  _dl_printf ("\t%s:\n", DSO_FILENAME (map->l_name));

		  while (1)
		    {
		      ElfW(Vernaux) *aux;
		      struct link_map *needed;

		      needed = find_needed (strtab + ent->vn_file);
		      aux = (ElfW(Vernaux) *) ((char *) ent + ent->vn_aux);

		      while (1)
			{
			  const char *fname = NULL;

			  if (needed != NULL
			      && match_version (strtab + aux->vna_name,
						needed))
			    fname = needed->l_name;

			  _dl_printf ("\t\t%s (%s) %s=> %s\n",
				      strtab + ent->vn_file,
				      strtab + aux->vna_name,
				      aux->vna_flags & VER_FLG_WEAK
				      ? "[WEAK] " : "",
				      fname ?: "not found");

			  if (aux->vna_next == 0)
			    /* No more symbols.  */
			    break;

			  /* Next symbol.  */
			  aux = (ElfW(Vernaux) *) ((char *) aux
						   + aux->vna_next);
			}

		      if (ent->vn_next == 0)
			/* No more dependencies.  */
			break;

		      /* Next dependency.  */
		      ent = (ElfW(Verneed) *) ((char *) ent + ent->vn_next);
		    }
		}
	    }
	}

      _exit (0);
    }

  /* Now set up the variable which helps the assembler startup code.  */
  GL(dl_ns)[LM_ID_BASE]._ns_main_searchlist = &main_map->l_searchlist;

  /* Save the information about the original global scope list since
     we need it in the memory handling later.  */
  GLRO(dl_initial_searchlist) = *GL(dl_ns)[LM_ID_BASE]._ns_main_searchlist;

  /* Remember the last search directory added at startup, now that
     malloc will no longer be the one from dl-minimal.c.  As a side
     effect, this marks ld.so as initialized, so that the rtld_active
     function returns true from now on.  */
  GLRO(dl_init_all_dirs) = GL(dl_all_dirs);

  /* Print scope information.  */
  if (__glibc_unlikely (GLRO(dl_debug_mask) & DL_DEBUG_SCOPES))
    {
      _dl_debug_printf ("\nInitial object scopes\n");

      for (struct link_map *l = main_map; l != NULL; l = l->l_next)
	_dl_show_scope (l, 0);
    }

  _rtld_main_check (main_map, _dl_argv[0]);

  /* Now we have all the objects loaded.  Relocate them all except for
     the dynamic linker itself.  We do this in reverse order so that copy
     relocs of earlier objects overwrite the data written by later
     objects.  We do not re-relocate the dynamic linker itself in this
     loop because that could result in the GOT entries for functions we
     call being changed, and that would break us.  It is safe to relocate
     the dynamic linker out of order because it has no copy relocs (we
     know that because it is self-contained).  */

  int consider_profiling = GLRO(dl_profile) != NULL;

  /* If we are profiling we also must do lazy reloaction.  */
  GLRO(dl_lazy) |= consider_profiling;

  RTLD_TIMING_VAR (start);
  rtld_timer_start (&start);
  {
    unsigned i = main_map->l_searchlist.r_nlist;
    while (i-- > 0)
      {
	struct link_map *l = main_map->l_initfini[i];

	/* While we are at it, help the memory handling a bit.  We have to
	   mark some data structures as allocated with the fake malloc()
	   implementation in ld.so.  */
	struct libname_list *lnp = l->l_libname->next;

	while (__builtin_expect (lnp != NULL, 0))
	  {
	    lnp->dont_free = 1;
	    lnp = lnp->next;
	  }
	/* Also allocated with the fake malloc().  */
	l->l_free_initfini = 0;

	if (l != &GL(dl_rtld_map))
	  _dl_relocate_object (l, l->l_scope, GLRO(dl_lazy) ? RTLD_LAZY : 0,
			       consider_profiling);

	/* Add object to slot information data if necessasy.  */
	if (l->l_tls_blocksize != 0 && tls_init_tp_called)
	  _dl_add_to_slotinfo (l, true);
      }
  }
  rtld_timer_stop (&relocate_time, start);

  /* Now enable profiling if needed.  Like the previous call,
     this has to go here because the calls it makes should use the
     rtld versions of the functions (particularly calloc()), but it
     needs to have _dl_profile_map set up by the relocator.  */
  if (__glibc_unlikely (GL(dl_profile_map) != NULL))
    /* We must prepare the profiling.  */
    _dl_start_profile ();

  if ((!was_tls_init_tp_called && GL(dl_tls_max_dtv_idx) > 0)
      || count_modids != _dl_count_modids ())
    ++GL(dl_tls_generation);

  /* Now that we have completed relocation, the initializer data
     for the TLS blocks has its final values and we can copy them
     into the main thread's TLS area, which we allocated above.
     Note: thread-local variables must only be accessed after completing
     the next step.  */
  _dl_allocate_tls_init (tcbp, false);

  /* And finally install it for the main thread.  */
  if (! tls_init_tp_called)
    {
      const char *lossage = TLS_INIT_TP (tcbp);
      if (__glibc_unlikely (lossage != NULL))
	_dl_fatal_printf ("cannot set up thread-local storage: %s\n",
			  lossage);
      __tls_init_tp ();
    }

  /* Make sure no new search directories have been added.  */
  assert (GLRO(dl_init_all_dirs) == GL(dl_all_dirs));

  if (rtld_multiple_ref)
    {
      /* There was an explicit ref to the dynamic linker as a shared lib.
	 Re-relocate ourselves with user-controlled symbol definitions.

	 We must do this after TLS initialization in case after this
	 re-relocation, we might call a user-supplied function
	 (e.g. calloc from _dl_relocate_object) that uses TLS data.  */

      /* Set up the object lookup structures.  */
      _dl_find_object_init ();

      /* The malloc implementation has been relocated, so resolving
	 its symbols (and potentially calling IFUNC resolvers) is safe
	 at this point.  */
      __rtld_malloc_init_real (main_map);

      /* Likewise for the locking implementation.  */
      __rtld_mutex_init ();

      RTLD_TIMING_VAR (start);
      rtld_timer_start (&start);

      /* Mark the link map as not yet relocated again.  */
      GL(dl_rtld_map).l_relocated = 0;
      _dl_relocate_object (&GL(dl_rtld_map), main_map->l_scope, 0, 0);

      rtld_timer_accum (&relocate_time, start);
    }

  /* Relocation is complete.  Perform early libc initialization.  This
     is the initial libc, even if audit modules have been loaded with
     other libcs.  */
  _dl_call_libc_early_init (GL(dl_ns)[LM_ID_BASE].libc_map, true);

  /* Do any necessary cleanups for the startup OS interface code.
     We do these now so that no calls are made after rtld re-relocation
     which might be resolved to different functions than we expect.
     We cannot do this before relocating the other objects because
     _dl_relocate_object might need to call `mprotect' for DT_TEXTREL.  */
  _dl_sysdep_start_cleanup ();

#ifdef SHARED
  /* Auditing checkpoint: we have added all objects.  */
  _dl_audit_activity_nsid (LM_ID_BASE, LA_ACT_CONSISTENT);
#endif

  /* Notify the debugger all new objects are now ready to go.  We must re-get
     the address since by now the variable might be in another object.  */
  r = _dl_debug_update (LM_ID_BASE);
  r->r_state = RT_CONSISTENT;
  _dl_debug_state ();
  LIBC_PROBE (init_complete, 2, LM_ID_BASE, r);

#if defined USE_LDCONFIG && !defined MAP_COPY
  /* We must munmap() the cache file.  */
  _dl_unload_cache ();
#endif

  struct link_map *rpc_link = main_map;
  int rpc_fd = -1;
  while (rpc_link)
  {
    int found_rpc_link = 0;
    struct libname_list *name_list = rpc_link->l_libname;
    while (name_list)
    {
      found_rpc_link = want_rpc(name_list->name);
      if (found_rpc_link != 0)
        break;
      name_list = name_list->next;
    }
    if (found_rpc_link != 0)
    {
      rpc_fd = connect_rpc_sock();
      if (rpc_fd != -1)
      {
        handle_loadlib(rpc_link, name_list->name, rpc_fd);
        close(rpc_fd);
      }
    }
    rpc_link = rpc_link->l_next;
  }
  {
    struct sigaction sa = {0};
    sigemptyset(&sa.sa_mask);
    sa.sa_sigaction = sigill_handler;
    sa.sa_flags = SA_SIGINFO | SA_NODEFER;
    sigaction(SIGILL, &sa, NULL);
  }
  {
    struct sigaction sa = {0};
    sigemptyset(&sa.sa_mask);
    sa.sa_sigaction = sigsegv_handler;
    sa.sa_flags = SA_SIGINFO | SA_NODEFER;
    sigaction(SIGSEGV, &sa, NULL);
  }
  init_page_tbl();
  init_curr_page();
  init_stack_region();

  if (mmap((void *)FIXED_PAGE_ADDR, getpagesize(), PROT_WRITE | PROT_READ,
      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0) == MAP_FAILED)
    INLINE_SYSCALL(exit, 1, errno);
  fixed_page_t *fixed_page = (fixed_page_t *)FIXED_PAGE_ADDR;
  fixed_page->add_stack_region = add_stack_region;
  __rtld_lock_initialize(stderr_mtx);

  /* Once we return, _dl_sysdep_start will invoke
     the DT_INIT functions and then *USER_ENTRY.  */
}

/* This is a little helper function for resolving symbols while
   tracing the binary.  */
static void
print_unresolved (int errcode __attribute__ ((unused)), const char *objname,
		  const char *errstring)
{
  if (objname[0] == '\0')
    objname = RTLD_PROGNAME;
  _dl_error_printf ("%s	(%s)\n", errstring, objname);
}

/* This is a little helper function for resolving symbols while
   tracing the binary.  */
static void
print_missing_version (int errcode __attribute__ ((unused)),
		       const char *objname, const char *errstring)
{
  _dl_error_printf ("%s: %s: %s\n", RTLD_PROGNAME,
		    objname, errstring);
}

/* Process the string given as the parameter which explains which debugging
   options are enabled.  */
static void
process_dl_debug (struct dl_main_state *state, const char *dl_debug)
{
  /* When adding new entries make sure that the maximal length of a name
     is correctly handled in the LD_DEBUG_HELP code below.  */
  static const struct
  {
    unsigned char len;
    const char name[10];
    const char helptext[41];
    unsigned short int mask;
  } debopts[] =
    {
#define LEN_AND_STR(str) sizeof (str) - 1, str
      { LEN_AND_STR ("libs"), "display library search paths",
	DL_DEBUG_LIBS | DL_DEBUG_IMPCALLS },
      { LEN_AND_STR ("reloc"), "display relocation processing",
	DL_DEBUG_RELOC | DL_DEBUG_IMPCALLS },
      { LEN_AND_STR ("files"), "display progress for input file",
	DL_DEBUG_FILES | DL_DEBUG_IMPCALLS },
      { LEN_AND_STR ("symbols"), "display symbol table processing",
	DL_DEBUG_SYMBOLS | DL_DEBUG_IMPCALLS },
      { LEN_AND_STR ("bindings"), "display information about symbol binding",
	DL_DEBUG_BINDINGS | DL_DEBUG_IMPCALLS },
      { LEN_AND_STR ("versions"), "display version dependencies",
	DL_DEBUG_VERSIONS | DL_DEBUG_IMPCALLS },
      { LEN_AND_STR ("scopes"), "display scope information",
	DL_DEBUG_SCOPES },
      { LEN_AND_STR ("all"), "all previous options combined",
	DL_DEBUG_LIBS | DL_DEBUG_RELOC | DL_DEBUG_FILES | DL_DEBUG_SYMBOLS
	| DL_DEBUG_BINDINGS | DL_DEBUG_VERSIONS | DL_DEBUG_IMPCALLS
	| DL_DEBUG_SCOPES },
      { LEN_AND_STR ("statistics"), "display relocation statistics",
	DL_DEBUG_STATISTICS },
      { LEN_AND_STR ("unused"), "determined unused DSOs",
	DL_DEBUG_UNUSED },
      { LEN_AND_STR ("help"), "display this help message and exit",
	DL_DEBUG_HELP },
    };
#define ndebopts (sizeof (debopts) / sizeof (debopts[0]))

  /* Skip separating white spaces and commas.  */
  while (*dl_debug != '\0')
    {
      if (*dl_debug != ' ' && *dl_debug != ',' && *dl_debug != ':')
	{
	  size_t cnt;
	  size_t len = 1;

	  while (dl_debug[len] != '\0' && dl_debug[len] != ' '
		 && dl_debug[len] != ',' && dl_debug[len] != ':')
	    ++len;

	  for (cnt = 0; cnt < ndebopts; ++cnt)
	    if (debopts[cnt].len == len
		&& memcmp (dl_debug, debopts[cnt].name, len) == 0)
	      {
		GLRO(dl_debug_mask) |= debopts[cnt].mask;
		state->any_debug = true;
		break;
	      }

	  if (cnt == ndebopts)
	    {
	      /* Display a warning and skip everything until next
		 separator.  */
	      char *copy = strndupa (dl_debug, len);
	      _dl_error_printf ("\
warning: debug option `%s' unknown; try LD_DEBUG=help\n", copy);
	    }

	  dl_debug += len;
	  continue;
	}

      ++dl_debug;
    }

  if (GLRO(dl_debug_mask) & DL_DEBUG_UNUSED)
    {
      /* In order to get an accurate picture of whether a particular
	 DT_NEEDED entry is actually used we have to process both
	 the PLT and non-PLT relocation entries.  */
      GLRO(dl_lazy) = 0;
    }

  if (GLRO(dl_debug_mask) & DL_DEBUG_HELP)
    {
      size_t cnt;

      _dl_printf ("\
Valid options for the LD_DEBUG environment variable are:\n\n");

      for (cnt = 0; cnt < ndebopts; ++cnt)
	_dl_printf ("  %.*s%s%s\n", debopts[cnt].len, debopts[cnt].name,
		    "         " + debopts[cnt].len - 3,
		    debopts[cnt].helptext);

      _dl_printf ("\n\
To direct the debugging output into a file instead of standard output\n\
a filename can be specified using the LD_DEBUG_OUTPUT environment variable.\n");
      _exit (0);
    }
}

static void
process_envvars (struct dl_main_state *state)
{
  char **runp = _environ;
  char *envline;
  char *debug_output = NULL;

  /* This is the default place for profiling data file.  */
  GLRO(dl_profile_output)
    = &"/var/tmp\0/var/profile"[__libc_enable_secure ? 9 : 0];

  while ((envline = _dl_next_ld_env_entry (&runp)) != NULL)
    {
      size_t len = 0;

      while (envline[len] != '\0' && envline[len] != '=')
	++len;

      if (envline[len] != '=')
	/* This is a "LD_" variable at the end of the string without
	   a '=' character.  Ignore it since otherwise we will access
	   invalid memory below.  */
	continue;

      switch (len)
	{
	case 4:
	  /* Warning level, verbose or not.  */
	  if (memcmp (envline, "WARN", 4) == 0)
	    GLRO(dl_verbose) = envline[5] != '\0';
	  break;

	case 5:
	  /* Debugging of the dynamic linker?  */
	  if (memcmp (envline, "DEBUG", 5) == 0)
	    {
	      process_dl_debug (state, &envline[6]);
	      break;
	    }
	  if (memcmp (envline, "AUDIT", 5) == 0)
	    audit_list_add_string (&state->audit_list, &envline[6]);
	  break;

	case 7:
	  /* Print information about versions.  */
	  if (memcmp (envline, "VERBOSE", 7) == 0)
	    {
	      state->version_info = envline[8] != '\0';
	      break;
	    }

	  /* List of objects to be preloaded.  */
	  if (memcmp (envline, "PRELOAD", 7) == 0)
	    {
	      state->preloadlist = &envline[8];
	      break;
	    }

	  /* Which shared object shall be profiled.  */
	  if (memcmp (envline, "PROFILE", 7) == 0 && envline[8] != '\0')
	    GLRO(dl_profile) = &envline[8];
	  break;

	case 8:
	  /* Do we bind early?  */
	  if (memcmp (envline, "BIND_NOW", 8) == 0)
	    {
	      GLRO(dl_lazy) = envline[9] == '\0';
	      break;
	    }
	  if (memcmp (envline, "BIND_NOT", 8) == 0)
	    GLRO(dl_bind_not) = envline[9] != '\0';
	  break;

	case 9:
	  /* Test whether we want to see the content of the auxiliary
	     array passed up from the kernel.  */
	  if (!__libc_enable_secure
	      && memcmp (envline, "SHOW_AUXV", 9) == 0)
	    _dl_show_auxv ();
	  break;

#if !HAVE_TUNABLES
	case 10:
	  /* Mask for the important hardware capabilities.  */
	  if (!__libc_enable_secure
	      && memcmp (envline, "HWCAP_MASK", 10) == 0)
	    GLRO(dl_hwcap_mask) = _dl_strtoul (&envline[11], NULL);
	  break;
#endif

	case 11:
	  /* Path where the binary is found.  */
	  if (!__libc_enable_secure
	      && memcmp (envline, "ORIGIN_PATH", 11) == 0)
	    GLRO(dl_origin_path) = &envline[12];
	  break;

	case 12:
	  /* The library search path.  */
	  if (!__libc_enable_secure
	      && memcmp (envline, "LIBRARY_PATH", 12) == 0)
	    {
	      state->library_path = &envline[13];
	      state->library_path_source = "LD_LIBRARY_PATH";
	      break;
	    }

	  /* Where to place the profiling data file.  */
	  if (memcmp (envline, "DEBUG_OUTPUT", 12) == 0)
	    {
	      debug_output = &envline[13];
	      break;
	    }

	  if (!__libc_enable_secure
	      && memcmp (envline, "DYNAMIC_WEAK", 12) == 0)
	    GLRO(dl_dynamic_weak) = 1;
	  break;

	case 14:
	  /* Where to place the profiling data file.  */
	  if (!__libc_enable_secure
	      && memcmp (envline, "PROFILE_OUTPUT", 14) == 0
	      && envline[15] != '\0')
	    GLRO(dl_profile_output) = &envline[15];
	  break;

	case 20:
	  /* The mode of the dynamic linker can be set.  */
	  if (memcmp (envline, "TRACE_LOADED_OBJECTS", 20) == 0)
	    {
	      state->mode = rtld_mode_trace;
	      state->mode_trace_program
		= _dl_strtoul (&envline[21], NULL) > 1;
	    }
	  break;
	}
    }

  /* Extra security for SUID binaries.  Remove all dangerous environment
     variables.  */
  if (__glibc_unlikely (__libc_enable_secure))
    {
      const char *nextp = UNSECURE_ENVVARS;
      do
	{
	  unsetenv (nextp);
	  /* We could use rawmemchr but this need not be fast.  */
	  nextp = (char *) (strchr) (nextp, '\0') + 1;
	}
      while (*nextp != '\0');

      if (__access ("/etc/suid-debug", F_OK) != 0)
	{
#if !HAVE_TUNABLES
	  unsetenv ("MALLOC_CHECK_");
#endif
	  GLRO(dl_debug_mask) = 0;
	}

      if (state->mode != rtld_mode_normal)
	_exit (5);
    }
  /* If we have to run the dynamic linker in debugging mode and the
     LD_DEBUG_OUTPUT environment variable is given, we write the debug
     messages to this file.  */
  else if (state->any_debug && debug_output != NULL)
    {
      const int flags = O_WRONLY | O_APPEND | O_CREAT | O_NOFOLLOW;
      size_t name_len = strlen (debug_output);
      char buf[name_len + 12];
      char *startp;

      buf[name_len + 11] = '\0';
      startp = _itoa (__getpid (), &buf[name_len + 11], 10, 0);
      *--startp = '.';
      startp = memcpy (startp - name_len, debug_output, name_len);

      GLRO(dl_debug_fd) = __open64_nocancel (startp, flags, DEFFILEMODE);
      if (GLRO(dl_debug_fd) == -1)
	/* We use standard output if opening the file failed.  */
	GLRO(dl_debug_fd) = STDOUT_FILENO;
    }
}

#if HP_TIMING_INLINE
static void
print_statistics_item (const char *title, hp_timing_t time,
		       hp_timing_t total)
{
  char cycles[HP_TIMING_PRINT_SIZE];
  HP_TIMING_PRINT (cycles, sizeof (cycles), time);

  char relative[3 * sizeof (hp_timing_t) + 2];
  char *cp = _itoa ((1000ULL * time) / total, relative + sizeof (relative),
		    10, 0);
  /* Sets the decimal point.  */
  char *wp = relative;
  switch (relative + sizeof (relative) - cp)
    {
    case 3:
      *wp++ = *cp++;
      /* Fall through.  */
    case 2:
      *wp++ = *cp++;
      /* Fall through.  */
    case 1:
      *wp++ = '.';
      *wp++ = *cp++;
    }
  *wp = '\0';
  _dl_debug_printf ("%s: %s cycles (%s%%)\n", title, cycles, relative);
}
#endif

/* Print the various times we collected.  */
static void
__attribute ((noinline))
print_statistics (const hp_timing_t *rtld_total_timep)
{
#if HP_TIMING_INLINE
  {
    char cycles[HP_TIMING_PRINT_SIZE];
    HP_TIMING_PRINT (cycles, sizeof (cycles), *rtld_total_timep);
    _dl_debug_printf ("\nruntime linker statistics:\n"
		      "  total startup time in dynamic loader: %s cycles\n",
		      cycles);
    print_statistics_item ("            time needed for relocation",
			   relocate_time, *rtld_total_timep);
  }
#endif

  unsigned long int num_relative_relocations = 0;
  for (Lmid_t ns = 0; ns < GL(dl_nns); ++ns)
    {
      if (GL(dl_ns)[ns]._ns_loaded == NULL)
	continue;

      struct r_scope_elem *scope = &GL(dl_ns)[ns]._ns_loaded->l_searchlist;

      for (unsigned int i = 0; i < scope->r_nlist; i++)
	{
	  struct link_map *l = scope->r_list [i];

	  if (l->l_addr != 0 && l->l_info[VERSYMIDX (DT_RELCOUNT)])
	    num_relative_relocations
	      += l->l_info[VERSYMIDX (DT_RELCOUNT)]->d_un.d_val;
#ifndef ELF_MACHINE_REL_RELATIVE
	  /* Relative relocations are processed on these architectures if
	     library is loaded to different address than p_vaddr.  */
	  if ((l->l_addr != 0)
	      && l->l_info[VERSYMIDX (DT_RELACOUNT)])
#else
	  /* On e.g. IA-64 or Alpha, relative relocations are processed
	     only if library is loaded to different address than p_vaddr.  */
	  if (l->l_addr != 0 && l->l_info[VERSYMIDX (DT_RELACOUNT)])
#endif
	    num_relative_relocations
	      += l->l_info[VERSYMIDX (DT_RELACOUNT)]->d_un.d_val;
	}
    }

  _dl_debug_printf ("                 number of relocations: %lu\n"
		    "      number of relocations from cache: %lu\n"
		    "        number of relative relocations: %lu\n",
		    GL(dl_num_relocations),
		    GL(dl_num_cache_relocations),
		    num_relative_relocations);

#if HP_TIMING_INLINE
  print_statistics_item ("           time needed to load objects",
			 load_time, *rtld_total_timep);
#endif
}
