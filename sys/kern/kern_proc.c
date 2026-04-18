/*-
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright (c) 1982, 1986, 1989, 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <sys/cdefs.h>
#include "opt_ddb.h"
#include "opt_ktrace.h"
#include "opt_kstack_pages.h"
#include "opt_stack.h"

#include <sys/param.h>
#include <sys/systm.h>
#include <sys/bitstring.h>
#include <sys/conf.h>
#include <sys/elf.h>
#include <sys/eventhandler.h>
#include <sys/exec.h>
#include <sys/fcntl.h>
#include <sys/ipc.h>
#include <sys/jail.h>
#include <sys/kernel.h>
#include <sys/limits.h>
#include <sys/lock.h>
#include <sys/loginclass.h>
#include <sys/malloc.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/mutex.h>
#include <sys/namei.h>
#include <sys/proc.h>
#include <sys/ptrace.h>
#include <sys/refcount.h>
#include <sys/resourcevar.h>
#include <sys/rwlock.h>
#include <sys/sbuf.h>
#include <sys/sysent.h>
#include <sys/sched.h>
#include <sys/shm.h>
#include <sys/smp.h>
#include <sys/stack.h>
#include <sys/stat.h>
#include <sys/dtrace_bsd.h>
#include <sys/sysctl.h>
#include <sys/filedesc.h>
#include <sys/tty.h>
#include <sys/signalvar.h>
#include <sys/sdt.h>
#include <sys/sx.h>
#include <sys/user.h>
#include <sys/vnode.h>
#include <sys/wait.h>
#ifdef KTRACE
#include <sys/ktrace.h>
#endif

#ifdef DDB
#include <ddb/ddb.h>
#endif

#include <vm/vm.h>
#include <vm/vm_param.h>
#include <vm/vm_extern.h>
#include <vm/pmap.h>
#include <vm/vm_map.h>
#include <vm/vm_object.h>
#include <vm/vm_page.h>
#include <vm/vm_pager.h>
#include <vm/vm_radix.h>
#include <vm/uma.h>

#include <fs/devfs/devfs.h>

#ifdef COMPAT_FREEBSD32
#include <compat/freebsd32/freebsd32.h>
#include <compat/freebsd32/freebsd32_util.h>
#endif

SDT_PROVIDER_DEFINE(proc);

MALLOC_DEFINE(M_SESSION, "session", "session header");
static MALLOC_DEFINE(M_PROC, "proc", "Proc structures");
MALLOC_DEFINE(M_SUBPROC, "subproc", "Proc sub-structures");

static void doenterpgrp(struct proc *, struct pgrp *);
static void orphanpg(struct pgrp *pg);
static void fill_kinfo_aggregate(struct proc *p, struct kinfo_proc *kp);
static void fill_kinfo_proc_only(struct proc *p, struct kinfo_proc *kp);
static void fill_kinfo_thread(struct thread *td, struct kinfo_proc *kp,
    int preferthread);
static void pgdelete(struct pgrp *);
static int pgrp_init(void *mem, int size, int flags);
static int proc_ctor(void *mem, int size, void *arg, int flags);
static void proc_dtor(void *mem, int size, void *arg);
static int proc_init(void *mem, int size, int flags);
static void proc_fini(void *mem, int size);
static void pargs_free(struct pargs *pa);

/*
 * Other process lists
 */
struct pidhashhead *pidhashtbl = NULL;
struct sx *pidhashtbl_lock;
u_long pidhash;
u_long pidhashlock;
struct pgrphashhead *pgrphashtbl;
u_long pgrphash;
struct proclist allproc = LIST_HEAD_INITIALIZER(allproc);
struct sx __exclusive_cache_line allproc_lock;
struct sx __exclusive_cache_line proctree_lock;
struct mtx __exclusive_cache_line ppeers_lock;
struct mtx __exclusive_cache_line procid_lock;
uma_zone_t proc_zone;
uma_zone_t pgrp_zone;

/*
 * The offset of various fields in struct proc and struct thread.
 * These are used by kernel debuggers to enumerate kernel threads and
 * processes.
 */
const int proc_off_p_pid = offsetof(struct proc, p_pid);
const int proc_off_p_comm = offsetof(struct proc, p_comm);
const int proc_off_p_list = offsetof(struct proc, p_list);
const int proc_off_p_hash = offsetof(struct proc, p_hash);
const int proc_off_p_threads = offsetof(struct proc, p_threads);
const int thread_off_td_tid = offsetof(struct thread, td_tid);
const int thread_off_td_name = offsetof(struct thread, td_name);
const int thread_off_td_oncpu = offsetof(struct thread, td_oncpu);
const int thread_off_td_pcb = offsetof(struct thread, td_pcb);
const int thread_off_td_plist = offsetof(struct thread, td_plist);

EVENTHANDLER_LIST_DEFINE(process_ctor);
EVENTHANDLER_LIST_DEFINE(process_dtor);
EVENTHANDLER_LIST_DEFINE(process_init);
EVENTHANDLER_LIST_DEFINE(process_fini);
EVENTHANDLER_LIST_DEFINE(process_exit);
EVENTHANDLER_LIST_DEFINE(process_fork);
EVENTHANDLER_LIST_DEFINE(process_exec);

int kstack_pages = KSTACK_PAGES;
SYSCTL_INT(_kern, OID_AUTO, kstack_pages, CTLFLAG_RDTUN | CTLFLAG_NOFETCH,
    &kstack_pages, 0,
    "Kernel stack size in pages");
static int vmmap_skip_res_cnt = 0;
SYSCTL_INT(_kern, OID_AUTO, proc_vmmap_skip_resident_count, CTLFLAG_RW,
    &vmmap_skip_res_cnt, 0,
    "Skip calculation of the pages resident count in kern.proc.vmmap");

CTASSERT(sizeof(struct kinfo_proc) == KINFO_PROC_SIZE);
#ifdef COMPAT_FREEBSD32
CTASSERT(sizeof(struct kinfo_proc32) == KINFO_PROC32_SIZE);
#endif
