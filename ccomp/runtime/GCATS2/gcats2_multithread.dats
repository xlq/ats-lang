(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2009

(* ****** ****** *)

#define ATSCCOMP_NAMESPACE "gcats2_multithread_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

extern
fun the_threadinfolst_suspend
  (pf: !the_threadinfolst_v | (*none*)):<> void
  = "gcats2_the_threadinfolst_suspend"

(* ****** ****** *)

%{^

typedef
struct threadinfo_struct {
  pthread_t pid ;
  void *stackbeg, *stackend ;
  struct threadinfo_struct *prev ;
  struct threadinfo_struct *next ;
} threadinfo ;

typedef threadinfo *threadinfolst ;
typedef threadinfo *threadinfoptr ;

static int the_nsuspended = 0 ;
static pthread_cond_t
the_nsuspended_iszero = PTHREAD_COND_INITIALIZER ;

threadinfolst the_threadinfolst ;

/*
** this variable possesses the fields: pid, stackbeg, stackend
*/
__thread threadinfo the_threadinfoslf ;

/* ****** ****** */

ats_void_type
gcats2_fprint_the_threadinfoslf_pid
  (ats_ptr_type out) {
  fprintf((FILE*)out, "%i", the_threadinfoslf.pid) ; return ;
} // end of [gcats2_fprint_the_threadinfoslf_pid]

/* ****** ****** */

// [signum] needs to be word-aligned
void SIGUSR1_handle (intptr_t signum) {
  jmp_buf reg_save ;
  setjmp(reg_save) ;
  asm volatile ("": : :"memory") ;
  sem_post(&the_gcsleep_semaphore) ;
  the_threadinfoslf.stackend = &signum ;
  gcats2_the_threadinfolst_lock_acquire() ;
  the_nsuspended -= 1 ;
  // so [stackend==0] indicates that a thread is not suspended
  the_threadinfoslf.stackend = (void*)0 ;
  if (!the_nsuspended) pthread_cond_signal (&the_nsuspended_iszero) ;
  gcats2_the_threadinfolst_lock_release() ;
  return ;
} /* end of [SIGUSR1_handle] */

/* ****** ****** */

/*
** implemented in [gcats2_top.dats]
*/
extern sem_t the_gcsleep_semaphore ;

ats_void_type
gcats2_the_threadinfolst_suspend () {
  int nother = 0 ;
  threadinfolst p_info = the_threadinfolst ;
  // [the_threadinfolst_lock] must be held
  while (p_info) {
    if (p_info != &the_threadinfoslf) {
      nother += 1 ; pthread_kill (p_info->pid, SIGUSR1) ;
    } // end of [if]
    p_info = p_info->next ;
  } // end of [while]
  the_nsuspended = nother ;
  while (nother) {
    sem_wait (&the_gcsleep_semaphore) ; nother -= 1 ;
  } // end of [while]
  return ;
} /* end of [gcats2_the_threadinfolst_suspend] */

ats_void_type
gcats2_the_threadinfolst_restart () {
  pthread_cond_wait (&the_nsuspended_iszero, &the_threadinfolst_lock) ;
  return ;
} /* end of [gcats2_the_threadinfolst_restart] */

/* ****** ****** */

ats_void_type
gcats2_threadinfo_insert () {
  the_threadinfoslf.pid = pthread_self() ;
/*
  fprintf(stderr, "gcats2_threadinfo_insert: pid = %i\n", the_threadinfoslf.pid) ;
*/
  gcats2_mystackbeg_set(gcats2_mystackdir_get()) ;
  the_threadinfoslf.stackbeg = gcats2_mystackbeg_get () ;
  the_threadinfoslf.stackend = (void*)0 ;
  the_threadinfoslf.prev = (threadinfolst)0 ;
  the_threadinfoslf.next = the_threadinfolst ;

  gcats2_the_threadinfolst_lock_acquire() ;
  the_threadinfolst->prev = &the_threadinfoslf ; the_threadinfolst = &the_threadinfoslf ;
  gcats2_the_threadinfolst_lock_release() ;
  return ;
} /* end of [gcats2_threadinfo_insert] */

ats_void_type
gcats2_threadinfo_remove () {
  threadinfolst _prev, _next ;
//
  the_threadinfolst_lock_acquire () ;
//
  _prev = the_threadinfoslf.prev ;
  _next = the_threadinfoslf.next ;
  if (_next) {
    _next->prev = _prev ;
  }
  if (_prev) {
    _prev->next = _next ;
  } else { // [the_threadinfolst_self] is the first
    the_threadinfolst = _next ;
  }
//
  the_threadinfolst_lock_release () ;
//
  return ;
} /* end of [gcats2_threadinfo_remove] */

/* ****** ****** */

%} // end of [%{^]

////

%{^

#include "gcats1.cats"

/* ****** ****** */

sem_t the_sleep_semaphore ;

void gc_sem_init () {
  sem_init(&the_sleep_semaphore, 0, 0); return ;
}

/* ****** ****** */

void SIGUSR1_handle (int signum) {
  jmp_buf reg_save ; sigset_t sigset ;
  the_threadinfolst_self_stack_end_set () ;
  setjmp(reg_save) ;

  asm volatile ("": : :"memory") ;
  sem_post(&the_sleep_semaphore) ;

  sigfillset(&sigset) ; // blocking all signals
  sigdelset(&sigset, SIGUSR2) ; // except [SIGUSR2]
  sigsuspend(&sigset) ; // go into suspension

  return ;
} /* end of [SIGUSR1_handle] */

void SIGUSR2_handle (int signum) { return ; }

void gc_signal_init () {
  int err = 0 ;
  struct sigaction action1, action2 ;
  sigset_t *action1_sa_mask, *action2_sa_mask ;

  action1.sa_handler = &SIGUSR1_handle ;
  action1_sa_mask = &(action1.sa_mask) ;
  sigemptyset (action1_sa_mask) ;
  sigaddset (action1_sa_mask, SIGUSR2) ; // blocking [SIGUSR2]
  action1.sa_flags = SA_RESTART ;
  err = sigaction (SIGUSR1, &action1, NULL) ;
  if (err < 0) {
    perror ("[sigaction] failed on [SIGUSR1]\n") ;
  }

  fprintf (stderr, "gc_signal_init: [SIGUSR1] has been initialized\n") ;

  action2.sa_handler = &SIGUSR2_handle ;
  action2_sa_mask = &(action2.sa_mask) ;
  sigemptyset (action2_sa_mask) ;
  sigaddset (action2_sa_mask, SIGUSR1) ; // blocking [SIGUSR1]
  err = sigaction (SIGUSR2, &action2, NULL) ;
  if (err < 0) {
    perror ("[sigaction] failed on [SIGUSR2]\n") ;
  }

  fprintf (stderr, "gc_signal_init: [SIGUSR2] has been initialized\n") ;

  return ;
} /* end of [gc_signal_init] */

/* ****** ****** */

%}

abstype threadinfolst (int)
typedef threadinfolst0 = [n:nat] threadinfolst (n)
typedef threadinfolst1 = [n:pos] threadinfolst (n)

extern fun gc_mark_threadinfo_freeitmlst
  (itms: freeitmlst0): void = "gc_mark_threadinfo_freeitmlst"

implement gc_mark_threadinfo_freeitmlst (itms) = begin
  if freeitmlst_is_cons (itms) then let
    val ptr = freeitmlst2ptr itms; var ofs: int = 0
    val chks = gc_ptr_is_valid (ptr, ofs)
    val chks = (
      if chunklst_is_cons chks then chks else begin
        prerr "GC: Fatal Error: [gc_mark_threadinfo_freeitmlst]";
        prerrf (": the pointer [%p] is invalid.", @(ptr));
        prerr_newline ();
        exit {chunklst1} (1)
      end
    ) : chunklst1
    val markbits = chunklst_markbits_get (chks)
    val () = // could this really happen?
      if MARK_GET (markbits, ofs) > 0 then begin
        // this could happen only if data is mistreated as a pointer!!!
        MARK_CLEAR (markbits, ofs); chunklst_markcnt_dec (chks)
      end
    val () = chunklst_freecnt_inc (chks) // preventing [chks] from being swept
  in
    gc_mark_threadinfo_freeitmlst (freeitmlst_tail_get itms)
  end // end of [if]
end // end of [gc_mark_threadinfo_freeitmlst]

(* ****** ****** *)

%{$

extern ats_ptr_type gc_stack_beg_get () ;
extern ats_void_type gc_stack_beg_set (ats_int_type dir) ;

extern __thread freeitmlst *the_freeitmlst_array ;

ats_void_type gc_threadinfo_init () {
  threadinfolst current ;

  // explicit allocation done to avoid a bug involving thread-local arrays 
  the_freeitmlst_array = calloc (FREEITMLST_ARRAYSIZE, sizeof(freeitmlst)) ;
  if (!the_freeitmlst_array) {
    fprintf (stderr, "GC Fatal Error: [gc_threadinfo_init]") ;
    fprintf (stderr, ": [malloc] failed: no memory for [the_freeitmlst_array].\n") ;
    exit (1) ;
  }

  current = (threadinfolst)malloc (sizeof(threadinfo)) ;
  if (!current) { fprintf (
      stderr, "GC Fatal Error: [gc_threadinfo_init]: [malloc] failed.\n"
    ) ; // end of [fprintf]
    exit (1) ;
  }

  /* thread-local: */ the_threadinfolst_self = current ;

  current->pid = pthread_self() ;

  fprintf (stdout, "gc_threadinfo_init: current->pid = %i\n", current->pid) ;

  gc_stack_beg_set (gc_stack_dir_get ()) ;
  current->stack_beg = gc_stack_beg_get () ;
  current->stack_end = (ats_ptr_type)0 ;

  current->prev = (threadinfolst)0 ;

  the_threadinfolst_lock_acquire () ;
  current->next = the_threadinfolst_fst ;
  if (the_threadinfolst_fst) the_threadinfolst_fst->prev = current ;
  the_threadinfolst_fst = current ;
  the_threadinfolst_lock_release () ;

  // [the_freeitmlst_array] is thread-local
  current->freeitmlst_array = the_freeitmlst_array ;

  fprintf (stdout, "gc_threadinfo_init: return\n") ;

  return ;
} /* gc_threadinfo_init */

ats_void_type gc_threadinfo_fini () {
  threadinfolst _prev, _next ;
  _prev = the_threadinfolst_self->prev ; _next = the_threadinfolst_self->next ;

  the_threadinfolst_lock_acquire () ;

  if (_next) {
    _next->prev = _prev ;
  }

  if (_prev) {
    _prev->next = _next ;
  } else { // [the_threadinfolst_self] is the first
    the_threadinfolst_fst = _next ;
  }

  the_threadinfolst_lock_release () ;
  free (the_threadinfolst_self) ;
  // explicit deallocation done to avoid a bug involving thread-local arrays 
  free (the_freeitmlst_array) ;

  return ;
} /* end of [gc_threadinfo_fini] */

%}

(* ****** ****** *)

%{$

static inline
ats_void_type
gc_mark_threadinfolst_one (threadinfolst infolst) {
  int i, dir ; freeitmlst *freeitmlst_array, *_fr, *_to ;

  /* scanning the thread freeitmlst array */

  i = 0; freeitmlst_array = infolst->freeitmlst_array ;
  while (i < FREEITMLST_ARRAYSIZE) {
    gc_mark_threadinfo_freeitmlst (*freeitmlst_array) ;
    i += 1 ; freeitmlst_array += 1 ;
  } /* end of [while] */

  /* scanning the thread stack */

  if (!infolst->stack_end) {
    fprintf (stderr, "GC Fatal Error: [gc_mark_threadinfolst_one]") ;
    fprintf (stderr, ": illegal stack info: infolst = %p\n", infolst) ;
    exit (1) ;
  }

  dir = gc_stack_dir_get () ; if (dir > 0) {
    _fr = infolst->stack_beg ; _to = infolst->stack_end - 1 ;
  } else {
    _to = infolst->stack_beg ; _fr = infolst->stack_end + 1 ;
  } // end of [if]

  while (_fr <= _to) {
    gc_mark_ptr (*_fr) ; _fr += 1 ; // termination: obvious
  } // end of [while]

  return ;
}

static inline
ats_void_type
gc_mark_threadinfolst_all (threadinfolst infolst) {
/*
    fprintf (stderr, "gc_mark_threadinfolst_all: the_threadinfolst_self = ");
    fprintf (stderr, "%p\n", the_threadinfolst_self) ;
*/
  while (infolst) {
/*
    fprintf (stderr, "gc_mark_threadinfolst_all: infolst = %p\n", infolst) ;
*/
    if (infolst != the_threadinfolst_self) gc_mark_threadinfolst_one (infolst) ;
    infolst = infolst->next ;
  }
  return ;
} /* end of [gc_mark_threadinfo_all] */

ats_void_type gc_mark_the_threadinfolst () {
  gc_mark_threadinfolst_all (the_threadinfolst_fst) ;
} /* end of [gc_mark_the_threadinfo] */

%}

(* ****** ****** *)

%{$

extern ats_void_type gc_aut_free (ats_ptr_type) ;
extern ats_void_type gc_man_free (ats_ptr_type) ;
extern ats_ptr_type gc_man_malloc_bsz (ats_int_type) ;

void* gc_pthread_stubfun (void *data0) {
  void **data ;
  void *(*start_routine)(void*), *arg, *ret ;
  int linclo ;

  data = (void**)data0 ;
  start_routine = (void *(*)(void*))(data[0]) ;
  arg = data[1] ;
  linclo = (int)(intptr_t)(data[2]) ;

  gc_man_free (data) ;

  gc_threadinfo_init () ;

  pthread_cleanup_push (gc_threadinfo_fini, (void*)0) ;

  // fprintf (stderr, "gc_pthread_clo: before call to [start_routine]\n") ;

  ret = start_routine (arg) ;

  // fprintf (stderr, "gc_pthread_clo: after call to [start_routine]\n") ;

  if (linclo) gc_aut_free (arg) ; // a linear closure call
  pthread_cleanup_pop (1) ; // [1] means pop and execute

  return ret ;
} /* end of [gc_pthread_stubfun] */

/* ****** ****** */

int gc_pthread_create_cloptr (
  ats_clo_ptr_type cloptr, pthread_t *pid_r, int detached, int linclo
) {
  void **data ; pthread_attr_t attr; pthread_t pid ; int ret ;

  data = gc_man_malloc_bsz (3 * sizeof(void*)) ;
  data[0] = cloptr->closure_fun ; data[1] = cloptr ; data[2] = (void*)(intptr_t)linclo ;

  if (detached) {
    pthread_attr_init (&attr);
    pthread_attr_setdetachstate (&attr, PTHREAD_CREATE_DETACHED) ;
    ret = pthread_create (&pid, &attr, &gc_pthread_stubfun, data) ;
  } else {
    ret = pthread_create (&pid, NULL, &gc_pthread_stubfun, data) ;
  }

  if (ret != 0) gc_man_free (data) ;

  if (pid_r) *pid_r = pid ;

  return ret ;
} /* end of [gc_pthread_create_cloptr] */

%}

(* ****** ****** *)

(* end of [gc_multithread.dats] *)
