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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [list.sats] starts!\n"

#endif

(* ****** ****** *)

%{#

#include "prelude/CATS/list.cats"

%}

(* ****** ****** *)

prfun list_length_is_nonnegative
  {a:t@ype} {n:int} (xs: list (a, n)): [n>=0] void

(* ****** ****** *)

exception ListSubscriptException

(* ****** ****** *)

// a casting function implemented in [prelude/DATS/list.dats]
castfn list_of_list_vt {a:t@ype}
  {n:nat} (xs: list_vt (a, n)):<> list (a, n)

(* ****** ****** *)

// implemented on top of [list_vt_of_arraysize]
fun{a:t@ype} list_of_arraysize
  {n:nat} (arrsz: arraysize (a, n)):<> list (a, n)

(* ****** ****** *)

fun{a:t@ype} list_app__main
  {v:view} {vt:viewtype} {f:eff}
  (pf: !v | xs: List a, f: (!v | a, !vt) -<fun,f> void, env: !vt)
  :<f> void

fun{a:t@ype} list_app_fun {f:eff}
  (xs: List a, f: a -<fun,f> void):<f> void

fun{a:t@ype} list_app_clo {f:eff}
  (xs: List a, f: &(a -<clo,f> void)):<f> void

fun{a:t@ype} list_app_cloptr {f:eff}
  (xs: List a, f: !(a -<cloptr,f> void)):<f> void

fun{a:t@ype} list_app_cloref {f:eff}
  (xs: List a, f: (a -<cloref,f> void)):<f> void

(*

symintr list_app
overload list_app with list_app_fun
overload list_app with list_app_clo
overload list_app with list_app_cloptr
overload list_app with list_app_cloref

*)

(* ****** ****** *)

fun{a1,a2:t@ype} list_app2__main
  {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , f: (!v | a1, a2, !vt) -<fun,f> void
  , env: !vt
  ) :<f> void

fun{a1,a2:t@ype} list_app2_fun {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: (a1, a2) -<fun,f> void):<f> void

fun{a1,a2:t@ype} list_app2_clo {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: &(a1, a2) -<clo,f> void):<f> void

fun{a1,a2:t@ype} list_app2_cloptr {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: !(a1, a2) -<cloptr,f> void):<f> void

fun{a1,a2:t@ype} list_app2_cloref {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: (a1, a2) -<cloref,f> void):<f> void

(*

symintr list_app2
overload list_app2 with list_app2_fun
overload list_app2 with list_app2_clo
overload list_app2 with list_app2_cloptr
overload list_app2 with list_app2_cloref

*)

(* ****** ****** *)

fun{a:t@ype} list_append {i,j:nat}
  (xs: list (a, i), ys: list (a, j)):<> list (a, i+j)
overload + with list_append

(* ****** ****** *)

fun{a1,a2:t@ype} list_assoc__main {v:view} {vt: viewtype} {eq:eff}
  (pf: !v | xs: List @(a1, a2), eq: (!v | a1, a1, !vt) -<fun, eq> bool, x: a1, env: !vt)
  :<eq> Option_vt a2

fun{a1,a2:t@ype} list_assoc_fun {eq:eff}
  (xs: List @(a1, a2), eq: (a1, a1) -<fun, eq> bool, x: a1)
  :<eq> Option_vt a2

fun{a1,a2:t@ype} list_assoc_clo {eq:eff}
  (xs: List @(a1, a2), eq: &(a1, a1) -<clo, eq> bool, x: a1)
  :<eq> Option_vt a2

fun{a1,a2:t@ype} list_assoc_cloptr {eq:eff}
  (xs: List @(a1, a2), eq: !(a1, a1) -<cloptr, eq> bool, x: a1)
  :<eq> Option_vt a2

fun{a1,a2:t@ype} list_assoc_cloref {eq:eff}
  (xs: List @(a1, a2), eq: (a1, a1) -<cloref, eq> bool, x: a1)
  :<eq> Option_vt a2

(* ****** ****** *)

fun{a:t@ype} list_concat (xs: List (List a)):<> List a

(* ****** ****** *)

fun{a:t@ype} list_drop {n,i:nat | i <= n}
  (xs: list (a, n), i: int i):<> list (a, n-i)

fun{a:t@ype} list_drop_exn {n,i:nat}
  (xs: list (a, n), i: int i):<!exn> [i <= n] list (a, n-i)

(* ****** ****** *)

fun{a:t@ype} list_exists__main {v:view} {vt:viewtype} {p:eff}
  (pf: !v | xs: List a, p: (!v | a, !vt) -<fun,p> bool, env: !vt):<p> bool

fun{a:t@ype} list_exists_fun {p:eff}
  (xs: List a, p: a -<p> bool):<p> bool

fun{a:t@ype} list_exists_clo {p:eff}
  (xs: List a, p: &a -<p,clo> bool):<p> bool

fun{a:t@ype} list_exists_cloptr {p:eff}
  (xs: List a, p: !a -<p,cloptr> bool):<p> bool

fun{a:t@ype} list_exists_cloref {p:eff}
  (xs: List a, p: a -<p,cloref> bool):<p> bool

(*

symintr list_exists
overload list_exists with list_exists_fun
overload list_exists with list_exists_clo
overload list_exists with list_exists_cloptr
overload list_exists with list_exists_cloref

*)

(* ****** ****** *)

fun{a1,a2:t@ype} list_exists2__main
  {v:view} {vt:viewtype} {n:nat} {p:eff} (
    pf: !v
  | xs1: list (a1, n)
  , xs2: list (a2, n)
  , p: (!v | a1, a2, !vt) -<fun,p> bool
  , env: !vt
  ) :<p> bool

fun{a1,a2:t@ype} list_exists2_fun {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: (a1, a2) -<p> bool):<p> bool

fun{a1,a2:t@ype} list_exists2_clo {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: &(a1, a2) -<clo,p> bool):<p> bool

fun{a1,a2:t@ype} list_exists2_cloptr {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: !(a1, a2) -<cloptr,p> bool):<p> bool

fun{a1,a2:t@ype} list_exists2_cloref {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: (a1, a2) -<cloref,p> bool):<p> bool

(*

symintr list_exists2
overload list_exists2 with list_exists2_fun
overload list_exists2 with list_exists2_fun
overload list_exists2 with list_exists2_cloptr
overload list_exists2 with list_exists2_cloref

*)

(* ****** ****** *)

fun{a:t@ype} list_extend {n:nat}
  (xs: list (a, n), y: a):<> list (a, n+1)

(* ****** ****** *)

fun{a:t@ype} list_filter__main {v:view} {vt:viewtype} {n:nat} {p:eff}
  (pf: !v | xs: list (a, n), p: (!v | a, !vt) -<fun,p> bool, env: !vt)
  :<p> [n':nat | n' <= n] list (a, n')

fun{a:t@ype} list_filter_fun {n:nat} {p:eff}
  (xs: list (a, n), p: a -<fun,p> bool):<p> [n':nat | n' <= n] list (a, n')

fun{a:t@ype} list_filter_clo {n:nat} {p:eff}
  (xs: list (a, n), p: &a -<clo,p> bool):<p> [n':nat | n' <= n] list (a, n')

fun{a:t@ype} list_filter_cloptr {n:nat} {p:eff}
  (xs: list (a, n), p: !a -<cloptr,p> bool):<p> [n':nat | n' <= n] list (a, n')

fun{a:t@ype} list_filter_cloref {n:nat} {p:eff}
  (xs: list (a, n), p: a -<cloref,p> bool):<p> [n':nat | n' <= n] list (a, n')

(* ****** ****** *)

fun{a:t@ype} list_find__main {v:view} {vt:viewtype} {p:eff}
  (pf: !v | xs: List a, p: (!v | a, !vt) -<fun,p> bool, env: !vt):<p> Option_vt a

fun{a:t@ype} list_find_fun {p:eff}
  (xs: List a, p: a -<fun,p> bool):<p> Option_vt a

fun{a:t@ype} list_find_clo {p:eff}
  (xs: List a, p: &a -<clo,p> bool):<p> Option_vt a

fun{a:t@ype} list_find_cloptr {p:eff}
  (xs: List a, p: !a -<cloptr,p> bool):<p> Option_vt a

fun{a:t@ype} list_find_cloref {p:eff}
  (xs: List a, p: a -<cloref,p> bool):<p> Option_vt a

(* ****** ****** *)

fun{init,a:t@ype} list_fold_left__main {v:view} {vt:viewtype} {f:eff}
  (pf: !v | f: (!v | init, a, !vt) -<fun,f> init, ini: init, xs: List a, env: !vt):<f> init

fun{init,a:t@ype} list_fold_left_fun {f:eff}
  (f: (init, a) -<fun,f> init, ini: init, xs: List a):<f> init

fun{init,a:t@ype} list_fold_left_clo {f:eff}
  (f: &(init, a) -<clo,f> init, ini: init, xs: List a):<f> init

fun{init,a:t@ype} list_fold_left_cloptr {f:eff}
  (f: !(init, a) -<cloptr,f> init, ini: init, xs: List a):<f> init

fun{init,a:t@ype} list_fold_left_cloref {f:eff}
  (f: (init, a) -<cloref,f> init, ini: init, xs: List a):<f> init

(* ****** ****** *)

fun{init,a1,a2:t@ype} list_fold2_left__main
  {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | f: (!v | init, a1, a2, !vt) -<fun,f> init
  , ini: init
  , xs1: list (a1, n)
  , xs2: list (a2, n)
  , env: !vt
  ) :<f> init

fun{init,a1,a2:t@ype} list_fold2_left_cloptr {n:nat} {f:eff}
  (f: !(init, a1, a2) -<cloptr,f> init, ini: init, xs1: list (a1, n), xs2: list (a2, n)):<f> init

fun{init,a1,a2:t@ype} list_fold2_left_cloref {n:nat} {f:eff}
  (f: (init, a1, a2) -<cloref,f> init, ini: init, xs1: list (a1, n), xs2: list (a2, n)):<f> init

(* ****** ****** *)

fun{a,sink:t@ype} list_fold_right__main {v:view} {vt:viewtype} {f:eff}
  (pf: !v | f: (!v | a, sink, !vt) -<fun,f> sink, xs: List a, ini: sink, env: !vt):<f> sink

fun{a,sink:t@ype} list_fold_right_fun {f:eff}
  (f: (a, sink) -<fun,f> sink, xs: List a, ini: sink):<f> sink

fun{a,sink:t@ype} list_fold_right_clo {f:eff}
  (f: &(a, sink) -<clo,f> sink, xs: List a, ini: sink):<f> sink

fun{a,sink:t@ype} list_fold_right_cloptr {f:eff}
  (f: !(a, sink) -<cloptr,f> sink, xs: List a, ini: sink):<f> sink

fun{a,sink:t@ype} list_fold_right_cloref {f:eff}
  (f: (a, sink) -<cloref,f> sink, xs: List a, ini: sink):<f> sink

(* ****** ****** *)

fun{a1,a2,sink:t@ype} list_fold2_right__main
  {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | f: (!v | a1, a2, sink, !vt) -<fun,f> sink
  , xs1: list (a1, n)
  , xs2: list (a2, n)
  , ini: sink
  , env: !vt
  ) :<f> sink

(* ****** ****** *)

fun{a:t@ype} list_forall__main {v:view} {vt:viewtype} {p:eff}
  (pf: !v | xs: List a, p: (!v | a, !vt) -<fun,p> bool, env: !vt):<p> bool

fun{a:t@ype} list_forall_fun {p:eff}
  (xs: List a, p: a -<p> bool):<p> bool

fun{a:t@ype} list_forall_clo {p:eff}
  (xs: List a, p: &a -<clo,p> bool):<p> bool

fun{a:t@ype} list_forall_cloptr {p:eff}
  (xs: List a, p: !a -<cloptr,p> bool):<p> bool

fun{a:t@ype} list_forall_cloref {p:eff}
  (xs: List a, p: a -<cloref,p> bool):<p> bool

(*

symintr list_forall
overload list_forall with list_forall_fun
overload list_forall with list_forall_clo
overload list_forall with list_forall_cloptr
overload list_forall with list_forall_cloref

*)

(* ****** ****** *)

fun{a1,a2:t@ype} list_forall2__main
  {v:view} {vt:viewtype} {n:nat} {p:eff} (
    pf: !v
  | xs1: list (a1, n)
  , xs2: list (a2, n)
  , p: (!v | a1, a2, !vt) -<fun,p> bool
  , env: !vt
  ) :<p> bool

fun{a1,a2:t@ype} list_forall2_fun {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: (a1, a2) -<p> bool):<p> bool

fun{a1,a2:t@ype} list_forall2_clo {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: &(a1, a2) -<p,clo> bool):<p> bool

fun{a1,a2:t@ype} list_forall2_cloptr {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: !(a1, a2) -<p,cloptr> bool):<p> bool

fun{a1,a2:t@ype} list_forall2_cloref {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: (a1, a2) -<p,cloref> bool):<p> bool

(*

symintr list_forall2
overload list_forall2 with list_forall2_fun
overload list_forall2 with list_forall2_clo
overload list_forall2 with list_forall2_cloptr
overload list_forall2 with list_forall2_cloref

*)

(* ****** ****** *)

fun{a:t@ype} list_foreach__main {v:view} {vt:viewtype} {f:eff}
  (pf: !v | xs: List a, f: (!v | a, !vt) -<fun,f> void, env: !vt):<f> void

fun{a:t@ype} list_foreach_fun {v:view} {f:eff}
  (pf: !v | xs: List a, f: (!v | a) -<fun,f> void):<f> void

fun{a:t@ype} list_foreach_clo {v:view} {f:eff}
  (pf: !v | xs: List a, f: &(!v | a) -<clo,f> void):<f> void

fun{a:t@ype} list_foreach_cloptr
  {f:eff} (xs: List a, f: !(a) -<cloptr,f> void):<f> void
// end of [list_foreach_cloptr]

fun{a:t@ype} list_foreach_cloref
  {f:eff} (xs: List a, f: (a) -<cloref,f> void):<f> void
// end of [list_foreach_cloref]

(* ****** ****** *)

fun{a1,a2:t@ype} list_foreach2__main
  {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , f: (!v | a1, a2, !vt) -<fun,f> void
  , env: !vt
  ) :<f> void

fun{a1,a2:t@ype} list_foreach2_fun {v:view} {n:nat} {f:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , f: (!v | a1, a2) -<fun,f> void
  ) :<f> void

fun{a1,a2:t@ype} list_foreach2_clo {v:view} {n:nat} {f:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , f: &(!v | a1, a2) -<clo,f> void
  ) :<f> void

fun{a1,a2:t@ype} list_foreach2_cloptr {n:nat} {f:eff} (
    xs: list (a1, n), ys: list (a2, n), f: !(a1, a2) -<cloptr,f> void
  ) :<f> void
// end of [list_foreach2_cloptr]

fun{a1,a2:t@ype} list_foreach2_cloref {n:nat} {f:eff} (
    xs: list (a1, n), ys: list (a2, n), f: (a1, a2) -<cloref,f> void
  ) :<f> void
// end of [list_foreach2_cloref]

(* ****** ****** *)

fun{a:t@ype} list_iforeach__main {v:view} {vt:viewtype} {n:nat} {f:eff}
  (pf: !v | xs: list (a, n), f: (!v | natLt n, a, !vt) -<fun,f> void, env: !vt)
  :<f> void

fun{a:t@ype} list_iforeach_fun {v:view} {n:nat} {f:eff}
  (pf: !v | xs: list (a, n), f: (!v | natLt n, a) -<fun,f> void):<f> void

fun{a:t@ype} list_iforeach_clo {v:view} {n:nat} {f:eff}
  (pf: !v | xs: list (a, n), f: &(!v | natLt n, a) -<clo,f> void):<f> void

fun{a:t@ype} list_iforeach_cloptr {n:nat} {f:eff}
  (xs: list (a, n), f: !(natLt n, a) -<cloptr,f> void):<f> void
// end of [list_iforeach_cloptr]

fun{a:t@ype} list_iforeach_cloref {n:nat} {f:eff}
  (xs: list (a, n), f: (natLt n, a) -<cloref,f> void):<f> void
// end of [list_iforeach_cloref]

(* ****** ****** *)

fun{a1,a2:t@ype} list_iforeach2__main {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , f: (!v | natLt n, a1, a2, !vt) -<fun,f> void
  , env: !vt
  ) :<f> void

fun{a1,a2:t@ype} list_iforeach2_fun {v:view} {n:nat} {f:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , f: (!v | natLt n, a1, a2) -<fun,f> void
  ) :<f> void

fun{a1,a2:t@ype} list_iforeach2_clo {v:view} {n:nat} {f:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , f: &(!v | natLt n, a1, a2) -<clo,f> void
  ) :<f> void

fun{a1,a2:t@ype} list_iforeach2_cloptr {n:nat} {f:eff} (
    xs: list (a1, n), ys: list (a2, n), f: !(natLt n, a1, a2) -<cloptr,f> void
  ) :<f> void

fun{a1,a2:t@ype} list_iforeach2_cloref {n:nat} {f:eff} (
    xs: list (a1, n), ys: list (a2, n), f: (natLt n, a1, a2) -<cloref,f> void
  ) :<f> void
// end of [list_iforeach2_cloref]

(* ****** ****** *)

fun{a:t@ype} list_get_elt_at {n:nat} (xs: list (a, n), i: natLt n):<> a
overload [] with list_get_elt_at

fun{a:t@ype} list_get_elt_at_exn
  {n:nat} (xs: list (a, n), i: Nat):<!exn> [n>0] a

fun{a:t@ype} list_get_elt_at_opt (xs: List a, i: Nat):<> Option_vt a

(* ****** ****** *)

fun{a:t@ype} list_head {n:pos} (xs: list (a, n)):<> a
fun{a:t@ype} list_head_exn {n:nat} (xs: list (a, n)):<!exn> [n>0] a

(* ****** ****** *)

// always inline
fun{} list_is_empty {a:t@ype} {n:nat} (xs: list (a, n)):<> bool (n == 0)
fun{} list_isnot_empty {a:t@ype} {n:nat} (xs: list (a, n)):<> bool (n > 0)
overload ~ with list_isnot_empty

(* ****** ****** *)

fun{a:t@ype} list_last {n:pos} (xs: list (a, n)):<> a
fun{a:t@ype} list_last_exn {n:nat} (xs: list (a, n)):<!exn> [n>0] a

(* ****** ****** *)

fun{a:t@ype} list_length {n:nat} (xs: list (a, n)):<> int n
overload length with list_length

(* ****** ****** *)

fun{a:t@ype} list_make_elt {n:nat} (x: a, n: int n):<> list (a, n)

(* ****** ****** *)

fun{a,b:t@ype} list_map__main
  {v:view} {vt:viewtype} {n:nat} {f:eff}
  (pf: !v | xs: list (a, n), f: (!v | a, !vt) -<fun,f> b, env: !vt)
  :<f> list (b, n)

fun{a,b:t@ype} list_map_fun {n:nat} {f:eff}
  (xs: list (a, n), f: a -<fun,f> b):<f> list (b, n)

fun{a,b:t@ype} list_map_clo {n:nat} {f:eff}
  (xs: list (a, n), f: &(a -<clo,f> b)):<f> list (b, n)

fun{a,b:t@ype} list_map_cloptr {n:nat} {f:eff}
  (xs: list (a, n), f: !(a -<cloptr,f> b)):<f> list (b, n)

fun{a,b:t@ype} list_map_cloref {n:nat} {f:eff}
  (xs: list (a, n), f: (a -<cloref,f> b)):<f> list (b, n)

(*

symintr list_map
overload list_map with list_map_fun
overload list_map with list_map_clo
overload list_map with list_map_cloptr
overload list_map with list_map_cloref

*)

(* ****** ****** *)

fun{a1,a2,b:t@ype} list_map2__main
  {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , f: (!v | a1, a2, !vt) -<fun,f> b
  , env: !vt
  ) :<f> list (b, n)

fun{a1,a2,b:t@ype} list_map2_fun {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: (a1, a2) -<fun,f> b):<f> list (b, n)

fun{a1,a2,b:t@ype} list_map2_clo {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: &(a1, a2) -<clo,f> b):<f> list (b, n)

fun{a1,a2,b:t@ype} list_map2_cloptr {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: !(a1, a2) -<cloptr,f> b):<f> list (b, n)

fun{a1,a2,b:t@ype} list_map2_cloref {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: (a1, a2) -<cloref,f> b):<f> list (b, n)

(*

symintr list_map2
overload list_map2 with list_map2_fun
overload list_map2 with list_map2_clo
overload list_map2 with list_map2_cloptr
overload list_map2 with list_map2_cloref

*)

(* ****** ****** *)

fun{a:t@ype} list_nth {n:nat} (xs: list (a, n), i: natLt n):<> a
fun{a:t@ype} list_nth_exn {n:nat} (xs: list (a, n), i: Nat):<!exn> [n>0] a
fun{a:t@ype} list_nth_opt (xs: List a, i: Nat):<> Option_vt a

(* ****** ****** *)

fun{a:t@ype} list_reverse_append {i,j:nat}
  (xs: list (a, i), ys: list (a, j)):<> list (a, i+j)

fun{a:t@ype} list_reverse {n:nat} (xs: list (a, n)):<> list (a, n)

(* ****** ****** *)

fun{a:t@ype} list_set_elt_at {n:nat}
  (xs: list (a, n), i: natLt n, x: a):<> list (a, n)
fun{a:t@ype} list_set_elt_at_exn {n:nat}
  (xs: list (a, n), i: Nat, x: a):<!exn> [n>0] list (a, n)
fun{a:t@ype} list_set_elt_at_opt {n:nat}
  (x: list (a, n), i: Nat, x: a):<> Option_vt (list (a, n))

(* ****** ****** *)

fun{a:t@ype} list_split_at {n,i:nat | i <= n}
  (xs: list (a, n), i: int i):<> (list (a, i), list (a, n-i))

fun{a:t@ype} list_take {n,i:nat | i <= n}
  (xs: list (a, n), i: int i):<> list (a, i)

fun{a:t@ype} list_take_exn {n,i:nat}
  (xs: list (a, n), i: int i):<!exn> [i <= n] list (a, i)

(* ****** ****** *)

// list_tabulate: try list_vt_tabulate

(* ****** ****** *)

fun{a:t@ype} list_tail {n:pos}
  (xs: list (a, n)):<> list (a, n-1)

fun{a:t@ype} list_tail_exn {n:nat}
  (xs: list (a, n)):<!exn> [n>0] list (a, n-1)

(* ****** ****** *)

fun{a,b:t@ype} list_zip {n:nat}
  (xs: list (a, n), ys: list (b, n)):<> list (@(a, b), n)

(* ****** ****** *)

fun{a,b,c:t@ype} list_zipwith_fun {n:nat} {f:eff}
  (xs: list (a, n), ys: list (b, n), f: (a, b) -<fun,f> c):<f> list (c, n)

fun{a,b,c:t@ype} list_zipwith_clo {n:nat} {f:eff}
  (xs: list (a, n), ys: list (b, n), f: &(a, b) -<clo,f> c):<f> list (c, n)

fun{a,b,c:t@ype} list_zipwith_cloptr {n:nat} {f:eff}
  (xs: list (a, n), ys: list (b, n), f: !(a, b) -<cloptr,f> c):<f> list (c, n)

fun{a,b,c:t@ype} list_zipwith_cloref {n:nat} {f:eff}
  (xs: list (a, n), ys: list (b, n), f: (a, b) -<cloref,f> c):<f> list (c, n)

(* ****** ****** *)

fun{a1,a2:t@ype} list_unzip {n:nat}
  (xys: list (@(a1, a2), n)):<> (list (a1, n), list (a2, n))
// end of [list_unzip]

(* ****** ****** *)

fun{a:t@ype} list_mergesort {env:viewtype} {n:nat} {lte:eff}
  (xs: list (a, n), lte: (a, a, !env) -<fun,lte> bool, env: !env)
  :<lte> list (a, n)

fun{a:t@ype} list_quicksort {env:viewtype} {n:nat} {lte:eff}
  (xs: list (a, n), lte: (a, a, !env) -<fun,lte> bool, env: !env)
  :<lte> list (a, n)

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [list.sats] finishes!\n"

#endif

(* end of [list.sats] *)
