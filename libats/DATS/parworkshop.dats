(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(*
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: March, 2010
**
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no need for dynamic loading

(* ****** ****** *)

staload LQ = "libats/SATS/linqueue_arr.sats"
staload _(*anon*) = "libats/DATS/linqueue_arr.dats"
stadef QUEUE = $LQ.QUEUE

(* ****** ****** *)

staload PTHREAD = "libc/SATS/pthread.sats"
stadef mutex = $PTHREAD.mutex_vt
stadef cond = $PTHREAD.cond_vt

(* ****** ****** *)

staload "libats/SATS/parworkshop.sats"

(* ****** ****** *)

%{^

extern ats_void_type
atslib_linqueue_arr_queue_initialize_tsz
  (ats_ptr_type pq, ats_size_type qsz, ats_size_type tsz) ;
// end of [atslib_linqueue_arr_queue_initialize_tsz]

ats_ptr_type
atslib_parworkshop_workshop_make_tsz (
  ats_size_type qsz, ats_fun_ptr_type fwork, ats_size_type tsz
) {
  atslib_parworkshop_WORKSHOP *p ;
  p = ATS_MALLOC (sizeof(atslib_parworkshop_WORKSHOP)) ;
  pthread_mutex_init (&p->WSmut, (pthread_mutexattr_t*)0) ;
  atslib_linqueue_arr_queue_initialize_tsz (&p->WQ, qsz, tsz) ;
  pthread_cond_init (&p->WQemp, (pthread_condattr_t*)0) ;
  pthread_cond_init (&p->WQful, (pthread_condattr_t*)0) ;
  p->nworker = 0 ;
  pthread_cond_init (&p->WSisz, (pthread_condattr_t*)0) ;
  p->npaused = 0 ;
  pthread_cond_init (&p->WSpaused, (pthread_condattr_t*)0) ;
  pthread_cond_init (&p->WSequ1, (pthread_condattr_t*)0) ;
  p->nblocked = 0 ;
  pthread_cond_init (&p->WSequ2, (pthread_condattr_t*)0) ;
  p->fwork = fwork ;
  p->refcount = 0 ;
  return (p) ;
} // end of [atslib_parworkshop_workshop_make_tsz]

%} // end of [%{^]

(* ****** ****** *)

%{^

ats_void_type
atslib_parworkshop_workshop_free_lin
  (ats_ptr_type p0, ats_int_type lin) {
  atslib_parworkshop_WORKSHOP *p = (atslib_parworkshop_WORKSHOP*)p0 ;
  atslib_linqueue_arr_QUEUE *p_WQ = &(p->WQ) ;
  pthread_mutex_lock (&p->WSmut);
  while (1) {
    if (p->nworker != 0) {
      pthread_cond_wait (&p->WSisz, &p->WSmut) ;
    } else {
      break ;
    } // end of [if]
  } // end of [while]
  // [p->WSmut] is held at this point
  if (lin && p_WQ->nitm != 0) {
    fprintf (stderr
    , "exit(ATS): [atslib_parworkshop_workshop_free_lin]: work queue is not empty\n"
    ) ; exit (1) ;
  } // end of [if]
  atslib_linqueue_arr_queue_uninitialize (p_WQ) ;
  pthread_mutex_destroy (&p->WSmut) ;
  pthread_cond_destroy (&p->WQemp) ;
  pthread_cond_destroy (&p->WQful) ;
  pthread_cond_destroy (&p->WSisz) ;
  pthread_cond_destroy (&p->WSpaused) ;
  pthread_cond_destroy (&p->WSequ1) ;
  pthread_cond_destroy (&p->WSequ2) ;
  ATS_FREE(p) ;
  return ;
} // end of [atslib_parworkshop_workshop_free_lin]

ats_void_type
atslib_parworkshop_workshop_free
  (ats_ptr_type p0) { atslib_parworkshop_workshop_free_lin (p0, 0) ; return ; }
// end of [atslib_parworkshop_workshop_free]

ats_void_type
atslib_parworkshop_workshop_free_vt_exn
  (ats_ptr_type p0) { atslib_parworkshop_workshop_free_lin (p0, 1) ; return ; }
// end of [atslib_parworkshop_workshop_free]

%} // end of [%{^]

(* ****** ****** *)

implement{a}
workshop_make (qsz, f) = workshop_make_tsz (qsz, f, sizeof<a>)
// end of [workshop_make]

(* ****** ****** *)

extern
fun workshop_fwork_get {a:viewt@ype} {l:addr}
  (ws: !WORKSHOPptr (a, l)):<> (!WORKSHOPptr (a, l), &a >> a?) -<fun> int
  = "atslib_parworkshop_workshop_fwork_get"
// end of [workshop_fwork_get]

(* ****** ****** *)

extern
fun workshop_nworker_inc
  {a:viewt@ype} {l:addr} (ws: !WORKSHOPptr (a, l)):<> void
  = "atslib_parworkshop_workshop_nworker_inc"
// end of [workshop_nworker_inc]

(* ****** ****** *)

viewtypedef WORKSHOP (a:viewt@ype) =
  $extype_struct "atslib_parworkshop_WORKSHOP" of {
//
// WSmut = $PTHREAD.mutex_vt
//
  WQ = $LQ.QUEUE (a)
, WQemp = $PTHREAD.cond_vt
, WQful = $PTHREAD.cond_vt
, nworker = int // number of workers affiliated with the workshop
, WSisz = $PTHREAD.cond_vt // nworker = 0
, npaused = int // number of workers paused
, WSpaused = $PTHREAD.cond_vt
, WSequ1 = $PTHREAD.cond_vt // npaused = nworker
, nblocked = int // number of workers blocked
, WSequ2 = $PTHREAD.cond_vt // nblocked = nworker
, fwork = {l:addr} (!WORKSHOPptr (a, l), &a >> a?) -<cloref> int
, refcount = int
} // end of [WORKSHOP]

(* ****** ****** *)

extern fun
workshop_acquire {a:viewt@ype} {l:addr}
  (ws: !WORKSHOPptr (a, l)):<> (WORKSHOP (a) @ l | ptr l)
  = "atslib_parworkshop_workshop_acquire"
// end of [workshop_wkqueue_acquire]

extern fun
workshop_release {a:viewt@ype} {l:addr}
  (pf: WORKSHOP (a) @ l | p_ws: ptr l):<> void
  = "atslib_parworkshop_workshop_release"
// end of [workshop_release]

(* ****** ****** *)

extern fun
workshop_WSmut_get
  {a:viewt@ype} {l:addr} (pf: !WORKSHOP (a) @ l | p: ptr l)
  :<> [l_mut:addr] (
    mutex (WORKSHOP a @ l) @ l_mut, minus (ptr l, mutex (WORKSHOP a @ l) @ l_mut)
  | ptr l_mut
  ) = "atslib_parworkshop_workshop_WSmut_get"
// end of [workshop_WSmut_get]

extern fun
workshop_WQemp_get
  {a:viewt@ype} {l:addr}
  (pf: !WORKSHOP (a) @ l | p: ptr l)
  :<> [l_emp:addr] (
    cond @ l_emp, minus (ptr l, cond @ l_emp) | ptr l_emp
  ) = "atslib_parworkshop_workshop_WQemp_get"
// end of [workshop_WQemp_get]

extern fun
workshop_WQful_get
  {a:viewt@ype} {l:addr}
  (pf: !WORKSHOP (a) @ l | p: ptr l)
  :<> [l_ful:addr] (
    cond @ l_ful, minus (ptr l, cond @ l_ful) | ptr l_ful
  ) = "atslib_parworkshop_workshop_WQful_get"
// end of [workshop_WQful_get]

(* ****** ****** *)

extern fun
workshop_WSisz_get
  {a:viewt@ype} {l:addr}
  (pf: !WORKSHOP (a) @ l | p: ptr l)
  :<> [l_isz:addr] (
    cond @ l_isz, minus (ptr l, cond @ l_isz) | ptr l_isz
  ) = "atslib_parworkshop_workshop_WSisz_get"
// end of [workshop_WSisz_get]

extern fun
workshop_WSpaused_get
  {a:viewt@ype} {l:addr}
  (pf: !WORKSHOP (a) @ l | p: ptr l)
  :<> [l_pau:addr] (
    cond @ l_pau, minus (ptr l, cond @ l_pau) | ptr l_pau
  ) = "atslib_parworkshop_workshop_WSpaused_get"
// end of [workshop_WSpaused_get]

extern fun
workshop_WSequ1_get
  {a:viewt@ype} {l:addr}
  (pf: !WORKSHOP (a) @ l | p: ptr l)
  :<> [l_equ:addr] (
    cond @ l_equ, minus (ptr l, cond @ l_equ) | ptr l_equ
  ) = "atslib_parworkshop_workshop_WSequ1_get"
// end of [workshop_WSequ1_get]

extern fun
workshop_WSequ2_get
  {a:viewt@ype} {l:addr}
  (pf: !WORKSHOP (a) @ l | p: ptr l)
  :<> [l_equ:addr] (
    cond @ l_equ, minus (ptr l, cond @ l_equ) | ptr l_equ
  ) = "atslib_parworkshop_workshop_WSequ2_get"
// end of [workshop_WSequ2_get]

(* ****** ****** *)

implement
workshop_nworker_get
  (ws) = nworker where {
  val (pf_ws | p_ws) = workshop_acquire (ws)
  val nworker = p_ws->nworker
  val () = workshop_release (pf_ws | p_ws)
} // end of [workshop_nworker_get]

implement
workshop_npaused_get
  (ws) = npaused where {
  val (pf_ws | p_ws) = workshop_acquire (ws)
  val npaused = p_ws->npaused
  val () = workshop_release (pf_ws | p_ws)
} // end of [workshop_npaused_get]

(* ****** ****** *)

extern
fun workshop_nworker_inc {a:viewt@ype}
  {l:addr} (ws: !WORKSHOPptr (a, l)):<> void

implement
workshop_nworker_inc (ws) = () where {
  val (pf_ws | p_ws) = workshop_acquire (ws)
  val () = p_ws->nworker := p_ws->nworker + 1
  val () = workshop_release (pf_ws | p_ws)
} // end of [workshop_nworker_inc]

(* ****** ****** *)

extern
fun workshop_ref {a:viewt@ype}
  {l:addr} (ws: !WORKSHOPptr (a, l)):<!ref> WORKSHOPptr (a, l)

implement
workshop_ref {a} {l} (ws) = ws where {
  val (pf_ws | p_ws) = workshop_acquire (ws)
  val () = p_ws->refcount := p_ws->refcount + 1
  val () = workshop_release (pf_ws | p_ws)
  val ws = __cast (ws) where {
    extern castfn __cast (ws: !WORKSHOPptr (a, l)):<> WORKSHOPptr (a, l)
  } // end of [val]
} // end of [workshop_ref]

(* ****** ****** *)

extern
fun workshop_unref
  {a:viewt@ype} {l:addr} (ws: WORKSHOPptr (a, l)):<!ref> void

implement
workshop_unref {a} {l} (ws) = () where {
  val (pf_ws | p_ws) = workshop_acquire (ws)
  val () = p_ws->refcount := p_ws->refcount - 1
  val () = workshop_release (pf_ws | p_ws)
  val _ptr = __cast (ws) where {
    extern castfn __cast (ws: WORKSHOPptr (a, l)):<> ptr l
  } // end of [val]
} // end of [workshop_unref]

(* ****** ****** *)

implement{a}
workshop_add_worker
  {l} (ws) = err where {
  viewtypedef env = WORKSHOPptr (a, l)
  fun worker (ws: env): void = let
    var wk = workshop_remove_work<a> (ws)
    val fwork = workshop_fwork_get (ws)
    val status = fwork (ws, wk)
  in
    case+ 0 of
    | _ when status > 0 => worker (ws)
    | _ when (status = 0) => let // status = 0
        val (pf_ws | p_ws) = workshop_acquire (ws)
        val nworker1 = p_ws->nworker - 1
        val () = p_ws->nworker := nworker1
        val () = if (nworker1 = 0) then
          $PTHREAD.pthread_cond_broadcast (p_ws->WSisz)
        val () = if (nworker1 = p_ws->npaused) then
          $PTHREAD.pthread_cond_broadcast (p_ws->WSequ1)
        val () = if (nworker1 = p_ws->nblocked) then
          $PTHREAD.pthread_cond_broadcast (p_ws->WSequ2)
        val () = workshop_release (pf_ws | p_ws)
        val () = workshop_unref (ws)
      in
        // the pthread exits normally
      end // end of [_]
    | _ => let // for handling uncommon requests
        viewdef V_ws = WORKSHOP a @ l
        val (pf_ws | p_ws) = workshop_acquire (ws)
        val npaused1 = p_ws->npaused + 1
        val () = p_ws->npaused := npaused1
        val nworker = p_ws->nworker
        val () = if (npaused1 = nworker) then
          $PTHREAD.pthread_cond_broadcast (p_ws->WSequ1)
        // end of [val]
        val [l_mut:addr] (pf_mut, fpf_mut | p_mut) =
          workshop_WSmut_get {a} {l} (pf_ws | p_ws)
        val [l_pau:addr] (pf_pau, fpf_pau | p_pau) = 
          workshop_WSpaused_get {a} {l} (pf_ws | p_ws)
        val () = $PTHREAD.pthread_cond_wait_mutex {V_ws} (pf_ws | !p_pau, !p_mut)
        prval () = minus_addback (fpf_mut, pf_mut | p_ws)
        prval () = minus_addback (fpf_pau, pf_pau | p_ws)
        val npaused = p_ws->npaused
        val () = p_ws->npaused := npaused - 1
        val () = workshop_release (pf_ws | p_ws)
      in
        worker (ws)
      end // end of [status < 0]
  end // end of [val]
  val ws_new = workshop_ref (ws)
  val err = $PTHREAD.pthread_create_detached {env} (worker, ws_new)
  val () = if err <> 0 then let
    // no new worker is added
    prval () = opt_unsome {env} (ws_new); val () = workshop_unref (ws_new)
  in
    // (*nothing*)
  end else let
    // a new worker is added successully
    val () = workshop_nworker_inc (ws)
    prval () = opt_unnone {env} (ws_new)
    prval () = cleanup_top {env} (ws_new)
  in
    // (*nothing*)
  end // end of [val]
} // end of [workshop_add_worker]

(* ****** ****** *)

implement{a}
workshop_add_nworker
  {l} {n} (ws, n) =
  loop (ws, n, 0, 0(*err*)) where {
  fun loop {i:nat | i <= n} .<n-i>. (
      ws: !WORKSHOPptr (a, l), n: int n, i: int i, err0: int
    ) : int =
    if i < n then let
      val err = workshop_add_worker (ws)
    in
      loop (ws, n, i+1, err0 + err)
    end else err0 // end of [if]
  // end of [loop]
} // end of [workshop_add_nworker]

(* ****** ****** *)

implement{a}
workshop_insert_work {l} (ws, wk) = let
(*
  val () = begin
    print "workshop_insert_work: start"; print_newline ()
  end // end of [val]
*)
  val (pf_ws | p_ws) = workshop_acquire (ws)
  viewdef V_ws = WORKSHOP a @ l
  fun loop
    (pf_ws: V_ws | p_ws: ptr l, wk: a): void = let
    val isful = $LQ.queue_is_full {a} (p_ws->WQ)
  in    
    if isful then let
      val [l_mut:addr] (pf_mut, fpf_mut | p_mut) =
        workshop_WSmut_get {a} {l} (pf_ws | p_ws)
      val [l_ful:addr] (pf_ful, fpf_ful | p_ful) = 
        workshop_WQful_get {a} {l} (pf_ws | p_ws)
      viewdef V_mut = mutex (WORKSHOP a @ l) @ l_mut
      val () = $PTHREAD.pthread_cond_wait_mutex {V_ws} (pf_ws | !p_ful, !p_mut)
      prval () = minus_addback (fpf_mut, pf_mut | p_ws)
      prval () = minus_addback (fpf_ful, pf_ful | p_ws)
    in
      loop (pf_ws | p_ws, wk)
    end else let
      val isemp =
        $LQ.queue_is_empty {a} (p_ws->WQ)
      // end of [val]
      val () = $LQ.queue_insert<a> (p_ws->WQ, wk)
      val () = if isemp then let
//
        val () = p_ws->nblocked := 0
//
        val [l_emp:addr] (pf_emp, fpf_emp | p_emp) = 
          workshop_WQemp_get {a} {l} (pf_ws | p_ws)
        val () = $PTHREAD.pthread_cond_broadcast (!p_emp)
        prval () = minus_addback (fpf_emp, pf_emp | p_ws)
      in
        // nothing
      end // end of [val]
      val () = workshop_release (pf_ws | p_ws)
    in
      // nothing
    end // end of [if]
  end (* end of [loop] *)
in
  loop (pf_ws | p_ws, wk)
end // end of [workshop_insert_work]

(* ****** ****** *)

implement{a}
workshop_remove_work {l} (ws) = let
  val (pf_ws | p_ws) = workshop_acquire (ws)
  viewdef V_ws = WORKSHOP a @ l
  fun loop
    (pf_ws: V_ws | p_ws: ptr l): a = let
    val isemp = $LQ.queue_is_empty {a} (p_ws->WQ)
  in    
    if isemp then let
//
      val nblock1 = p_ws->nblocked + 1
      val () = p_ws->nblocked := nblock1
      val () = if (nblock1 = p_ws->nworker)
        then $PTHREAD.pthread_cond_broadcast (p_ws->WSequ2)
      // end of [val]
//
      val [l_mut:addr] (pf_mut, fpf_mut | p_mut) =
        workshop_WSmut_get {a} {l} (pf_ws | p_ws)
      val [l_emp:addr] (pf_emp, fpf_emp | p_emp) = 
        workshop_WQemp_get {a} {l} (pf_ws | p_ws)
      viewdef V_mut = mutex (WORKSHOP a @ l) @ l_mut
      val () = $PTHREAD.pthread_cond_wait_mutex {V_ws} (pf_ws | !p_emp, !p_mut)
      prval () = minus_addback (fpf_mut, pf_mut | p_ws)
      prval () = minus_addback (fpf_emp, pf_emp | p_ws)
    in
      loop (pf_ws | p_ws)
    end else let
      val isful =
        $LQ.queue_is_full {a} (p_ws->WQ)
      // end of [val]
      val wk = $LQ.queue_remove<a> (p_ws->WQ)
      val () = if isful then let
        val [l_ful:addr] (pf_ful, fpf_ful | p_ful) = 
          workshop_WQful_get {a} {l} (pf_ws | p_ws)
        val () = $PTHREAD.pthread_cond_broadcast (!p_ful)
        prval () = minus_addback (fpf_ful, pf_ful | p_ws)
      in
        // nothing
      end // end of [val]
      val () = workshop_release (pf_ws | p_ws)
    in
      wk (* return value *)
    end // end of [if]
  end (* end of [loop] *)
in
  loop (pf_ws | p_ws)
end // end of [workshop_remove_work]

(* ****** ****** *)

implement
workshop_wait_worker_quit
  {a} {l} (ws) = () where {
  viewdef V_ws = WORKSHOP a @ l
  val (pf_ws | p_ws) = workshop_acquire (ws)
  fun loop (
       pf_ws: !V_ws | p_ws: ptr l
     ) : void = let
    val nworker = p_ws->nworker
  in
    if nworker > 0 then let
      val (pf_mut, fpf_mut | p_mut) = workshop_WSmut_get (pf_ws | p_ws)
      val (pf_isz, fpf_isz | p_isz) = workshop_WSisz_get (pf_ws | p_ws)
      val () = $PTHREAD.pthread_cond_wait_mutex {V_ws} (pf_ws | !p_isz, !p_mut)
      prval () = minus_addback (fpf_mut, pf_mut | p_ws)
      prval () = minus_addback (fpf_isz, pf_isz | p_ws)
    in
      loop (pf_ws | p_ws)
    end else () // end of [if]
  end // end of [loop]
  val () = loop (pf_ws | p_ws)
  val () = workshop_release (pf_ws | p_ws)
} // end of [workshop_wait_worker_quit]

implement
workshop_wait_worker_paused
  {a} {l} (ws) = () where {
  viewdef V_ws = WORKSHOP a @ l
  val (pf_ws | p_ws) = workshop_acquire (ws)
  fun loop (
       pf_ws: !V_ws | p_ws: ptr l
     ) : void = let
    val nworker = p_ws->nworker
    val npaused = p_ws->npaused
  in
    if nworker > npaused then let
      val (pf_mut, fpf_mut | p_mut) = workshop_WSmut_get (pf_ws | p_ws)
      val (pf_equ, fpf_equ | p_equ) = workshop_WSequ1_get (pf_ws | p_ws)
      val () = $PTHREAD.pthread_cond_wait_mutex {V_ws} (pf_ws | !p_equ, !p_mut)
      prval () = minus_addback (fpf_mut, pf_mut | p_ws)
      prval () = minus_addback (fpf_equ, pf_equ | p_ws)
    in
      loop (pf_ws | p_ws)
    end else () // end of [if]
  end // end of [loop]
  val () = loop (pf_ws | p_ws)
  val () = workshop_release (pf_ws | p_ws)
} // end of [workshop_wait_worker_paused]

implement
workshop_resume_worker_paused
  {a} {l} (ws) = () where {
  viewdef V_ws = WORKSHOP a @ l
  val (pf_ws | p_ws) = workshop_acquire (ws)
  val () = $PTHREAD.pthread_cond_broadcast (p_ws->WSpaused)
  val () = workshop_release (pf_ws | p_ws)
} // end of [workshop_wait_worker_paused]

(* ****** ****** *)

implement
workshop_wait_worker_blocked
  {a} {l} (ws) = () where {
  viewdef V_ws = WORKSHOP a @ l
  val (pf_ws | p_ws) = workshop_acquire (ws)
  fun loop (
       pf_ws: !V_ws | p_ws: ptr l
     ) : void = let
    val nworker = p_ws->nworker
    val nblocked = p_ws->nblocked
  in
    if nworker > nblocked then let
      val (pf_mut, fpf_mut | p_mut) = workshop_WSmut_get (pf_ws | p_ws)
      val (pf_equ, fpf_equ | p_equ) = workshop_WSequ2_get (pf_ws | p_ws)
      val () = $PTHREAD.pthread_cond_wait_mutex {V_ws} (pf_ws | !p_equ, !p_mut)
      prval () = minus_addback (fpf_mut, pf_mut | p_ws)
      prval () = minus_addback (fpf_equ, pf_equ | p_ws)
    in
      loop (pf_ws | p_ws)
    end else () // end of [if]
  end // end of [loop]
  val () = loop (pf_ws | p_ws)
  val () = workshop_release (pf_ws | p_ws)
} // end of [workshop_wait_worker_blocked]

(* ****** ****** *)

(* end of [parworkshop.dats] *)
