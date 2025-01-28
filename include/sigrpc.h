/* SigRPC header file.
   This file defines the prototype implementation for SigRPC,
   designed for experimental purposes.
   Copyright (C) 2025 Keita HAGIWARA. All rights reserved.
   This file is not part of the official GNU C Library.

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

#ifndef SIGRPC_H
#define SIGRPC_H
#include <alloca.h>
#include <unistd.h>
#include <stdint.h>
#include <errno.h>

#define RPC_HEADER_SIZE (sizeof(uint32_t) + sizeof(int32_t) + sizeof(pid_t) + sizeof(uint64_t))

#define FIXED_PAGE_ADDR 0x40000000

#define MMAP_BASE 0x300000000000

typedef struct fixed_page_s {
  void (*add_stack_region)(void *end);
} fixed_page_t;

#define STATUS_OK 0
#define STATUS_NOT_FOUND 5
#define STATUS_INTERNAL 13
#define STATUS_DATALOSS 15

enum {
  LOADLIB = 0,
  INVOKEFUNC,
  PULLPAGE,
};

typedef struct rpc_msg_header_s {
  uint32_t msg_type;
  int32_t status;
  pid_t client_id;
  uint64_t payload_size;
} rpc_msg_header_t;

#endif
