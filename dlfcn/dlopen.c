/* Load a shared object at run time.
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

#include <dlfcn.h>
#include <libintl.h>
#include <stddef.h>
#include <unistd.h>
#include <ldsodefs.h>
#include <shlib-compat.h>

struct dlopen_args
{
  /* The arguments for dlopen_doit.  */
  const char *file;
  int mode;
  /* The return value of dlopen_doit.  */
  void *new;
  /* Address of the caller.  */
  const void *caller;
};


/* Non-shared code has no support for multiple namespaces.  */
#ifdef SHARED
# define NS __LM_ID_CALLER
#else
# define NS LM_ID_BASE
#endif


static void
dlopen_doit (void *a)
{
  struct dlopen_args *args = (struct dlopen_args *) a;

  if (args->mode & ~(RTLD_BINDING_MASK | RTLD_NOLOAD | RTLD_DEEPBIND
		     | RTLD_GLOBAL | RTLD_LOCAL | RTLD_NODELETE
		     | __RTLD_SPROF))
    _dl_signal_error (0, NULL, NULL, _("invalid mode parameter"));

  args->new = GLRO(dl_open) (args->file ?: "", args->mode | __RTLD_DLOPEN,
			     args->caller,
			     args->file == NULL ? LM_ID_BASE : NS,
			     __libc_argc, __libc_argv, __environ);
}


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
  {
	  errno = 0;
	  return 0;
  }
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
}

static void *
dlopen_implementation (const char *file, int mode, void *dl_caller)
{
  struct dlopen_args args;
  args.file = file;
  args.mode = mode;
  args.caller = dl_caller;

  struct link_map *map = _dlerror_run (dlopen_doit, &args) ? NULL : args.new;

  if (!map)
    return map;
  if (!want_rpc(file))
    return map;
  int rpc_fd = connect_rpc_sock();
  handle_loadlib(map, file, rpc_fd);
  close(rpc_fd);

  return map;
}

#ifdef SHARED
void *
___dlopen (const char *file, int mode)
{
  if (GLRO (dl_dlfcn_hook) != NULL)
    return GLRO (dl_dlfcn_hook)->dlopen (file, mode, RETURN_ADDRESS (0));
  else
    return dlopen_implementation (file, mode, RETURN_ADDRESS (0));
}
versioned_symbol (libc, ___dlopen, dlopen, GLIBC_2_34);

# if OTHER_SHLIB_COMPAT (libdl, GLIBC_2_1, GLIBC_2_34)
compat_symbol (libdl, ___dlopen, dlopen, GLIBC_2_1);
# endif
#else /* !SHARED */
/* Also used with _dlfcn_hook.  */
void *
__dlopen (const char *file, int mode, void *dl_caller)
{
  return dlopen_implementation (file, mode, RETURN_ADDRESS (0));
}

void *
___dlopen (const char *file, int mode)
{
  return __dlopen (file, mode, RETURN_ADDRESS (0));
}
weak_alias (___dlopen, dlopen)
static_link_warning (dlopen)
#endif /* !SHARED */
