(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
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

exception ListSubscriptException

(* ****** ****** *)

fun list_of_list_vt {a:t@ype}
  {n:nat} (xs: list_vt (a, n)):<> list (a, n)
  = "atspre_list_of_list_vt"

(* ****** ****** *)

fun{a:t@ype} list_of_arraysize
  {n:nat} (arrsz: arraysize (a, n)):<> list (a, n)

(* ****** ****** *)

fun{a:t@ype} list_append {i,j:nat}
  (xs: list (a, i), ys: list (a, j)):<> list (a, i+j)
overload + with list_append

(* ****** ****** *)

fun{a1,a2:t@ype} list_assoc_fun {eq:eff}
  (xs: List '(a1, a2), eq: (a1, a1) -<fun, eq> bool, x: a1)
  :<eq,!exn> Option a2

(* ****** ****** *)

fun{a:t@ype} list_concat (xs: List (List a)):<> List a

(* ****** ****** *)

fun{a:t@ype} list_drop {n,i:nat | i <= n}
  (xs: list (a, n), i: int i):<> list (a, n-i)

fun{a:t@ype} list_drop_exn {n,i:nat}
  (xs: list (a, n), i: int i):<!exn> [i <= n] list (a, n-i)

(* ****** ****** *)

fun{a:t@ype} list_exists_main {v:view} {vt:viewtype} {p:eff}
  (pf: !v | xs: List a, p: (!v | a, !vt) -<fun,p> bool, env: !vt):<p> bool

symintr list_exists

fun{a:t@ype} list_exists_fun {p:eff}
  (xs: List a, p: a -<p> bool):<p> bool
overload list_exists with list_exists_fun

fun{a:t@ype} list_exists_cloptr {p:eff}
  (xs: List a, p: !a -<p,cloptr> bool):<p> bool
overload list_exists with list_exists_cloptr

fun{a:t@ype} list_exists_cloref {p:eff}
  (xs: List a, p: a -<p,cloref> bool):<p> bool
overload list_exists with list_exists_cloref

(* ****** ****** *)

fun{a1,a2:t@ype} list_exists2_main
  {v:view} {vt:viewtype} {n:nat} {p:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , p: (!v | a1, a2, !vt) -<fun,p> bool
  , env: !vt
  ):<p> bool

symintr list_exists2

fun{a1,a2:t@ype} list_exists2_fun {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: (a1, a2) -<p> bool):<p> bool
overload list_exists2 with list_exists2_fun

fun{a1,a2:t@ype} list_exists2_cloptr {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: !(a1, a2) -<p,cloptr> bool):<p> bool
overload list_exists2 with list_exists2_cloptr

fun{a1,a2:t@ype} list_exists2_cloref {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: !(a1, a2) -<p,cloref> bool):<p> bool
overload list_exists2 with list_exists2_cloref

(* ****** ****** *)

fun{a:t@ype} list_filter_cloptr {n:nat} {p:eff}
  (xs: list (a, n), p: !a -<cloptr,p> bool):<p> [n':nat | n' <= n] list (a, n')

fun{a:t@ype} list_find_cloptr {p:eff}
  (xs: List a, p: !a -<cloptr,p> bool):<p> Option a

(* ****** ****** *)

fun{sink,a:t@ype} list_fold_left_cloptr {f:eff}
  (f: !(sink, a) -<cloptr,f> sink, ini: sink, xs: List a):<f> sink

fun{sink,a1,a2:t@ype} list_fold2_left_cloptr {n:nat} {f:eff}
  (f: !(sink, a1, a2) -<cloptr,f> sink, ini: sink, xs: list (a1, n), ys: list (a2, n))
  :<f> sink

fun{a,sink:t@ype} list_fold_right_cloptr {f:eff}
  (f: !(a, sink) -<cloptr,f> sink, xs: List a, ini: sink):<f> sink

fun{a1,a2,sink:t@ype} list_fold2_right_cloptr {n:nat} {f:eff}
  (f: !(a1, a2, sink) -<cloptr,f> sink, xs: list (a1, n), ys: list (a2, n), ini: sink)
  :<f> sink

(* ****** ****** *)

fun{a:t@ype} list_forall_main {v:view} {vt:viewtype} {p:eff}
  (pf: !v | xs: List a, p: (!v | a, !vt) -<fun,p> bool, env: !vt):<p> bool

symintr list_forall

fun{a:t@ype} list_forall_fun {p:eff}
  (xs: List a, p: a -<p> bool):<p> bool
overload list_forall with list_forall_fun

fun{a:t@ype} list_forall_cloptr {p:eff}
  (xs: List a, p: !a -<p,cloptr> bool):<p> bool
overload list_forall with list_forall_cloptr

fun{a:t@ype} list_forall_cloref {p:eff}
  (xs: List a, p: a -<p,cloref> bool):<p> bool
overload list_forall with list_forall_cloref

(* ****** ****** *)

fun{a1,a2:t@ype} list_forall2_main
  {v:view} {vt:viewtype} {n:nat} {p:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , p: (!v | a1, a2, !vt) -<fun,p> bool
  , env: !vt
  ):<p> bool

symintr list_forall2

fun{a1,a2:t@ype} list_forall2_fun {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: (a1, a2) -<p> bool):<p> bool
overload list_forall2 with list_forall2_fun

fun{a1,a2:t@ype} list_forall2_cloptr {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: !(a1, a2) -<p,cloptr> bool):<p> bool
overload list_forall2 with list_forall2_cloptr

fun{a1,a2:t@ype} list_forall2_cloref {n:nat} {p:eff}
  (xs: list (a1, n), ys: list (a2, n), p: !(a1, a2) -<p,cloref> bool):<p> bool
overload list_forall2 with list_forall2_cloref

(* ****** ****** *)

fun{a:t@ype} list_foreach_main {v:view} {vt:viewtype} {f:eff}
  (pf: !v | xs: List a, f: (!v | a, !vt) -<fun,f> void, env: !vt):<f> void

fun{a:t@ype} list_foreach_fun {f:eff}
  (xs: List a, f: a -<fun,f> void):<f> void

fun{a:t@ype} list_foreach_cloptr {f:eff}
  (xs: List a, f: !a -<cloptr,f> void):<f> void

fun{a:t@ype} list_foreach_cloref {f:eff}
  (xs: List a, f: !a -<cloref,f> void):<f> void

(* ****** ****** *)

fun{a1,a2:t@ype} list_foreach2_main
  {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , f: (!v | a1, a2, !vt) -<fun,f> void
  , env: !vt
  ) :<f> void

fun{a1,a2:t@ype} list_foreach2_fun {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: !(a1, a2) -<fun,f> void):<f> void

fun{a1,a2:t@ype} list_foreach2_cloptr {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: !(a1, a2) -<cloptr,f> void):<f> void

(* ****** ****** *)

fun{a:t@ype} list_iforeach_cloptr {n:nat} {f:eff}
  (xs: list (a, n), f: !(natLt n, a) -<cloptr,f> void):<f> void

fun{a1,a2:t@ype} list_iforeach2_cloptr {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: !(natLt n, a1, a2) -<cloptr,f> void)
  :<f> void

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

fun list_is_empty {a:t@ype} {n:nat} (xs: list (a, n)):<> bool (n == 0)
fun list_is_not_empty {a:t@ype} {n:nat} (xs: list (a, n)):<> bool (n > 0)
overload ~ with list_is_not_empty

(* ****** ****** *)

fun{a:t@ype} list_length {n:nat} (xs: list (a, n)):<> int n
overload length with list_length

(* ****** ****** *)

fun{a:t@ype} list_make_elt {n:nat} (x: a, n: int n):<> list (a, n)

(* ****** ****** *)

fun{a,b:t@ype} list_map_main
  {v:view} {vt:viewtype} {n:nat} {f:eff}
  (pf: !v | xs: list (a, n), f: (!v | a, !vt) -<fun,f> b, env: !vt)
  :<f> list (b, n)

symintr list_map

fun{a,b:t@ype} list_map_fun {n:nat} {f:eff}
  (xs: list (a, n), f: a -<fun,f> b):<f> list (b, n)
overload list_map with list_map_fun

fun{a,b:t@ype} list_map_cloptr {n:nat} {f:eff}
  (xs: list (a, n), f: !(a -<cloptr,f> b)):<f> list (b, n)
overload list_map with list_map_cloptr

fun{a,b:t@ype} list_map_cloref {n:nat} {f:eff}
  (xs: list (a, n), f: (a -<cloref,f> b)):<f> list (b, n)
overload list_map with list_map_cloref

(* ****** ****** *)

fun{a1,a2,b:t@ype} list_map2_main
  {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | xs: list (a1, n)
  , ys: list (a2, n)
  , f: (!v | a1, a2, !vt) -<fun,f> b
  , env: !vt
  ) :<f> list (b, n)

symintr list_map2

fun{a1,a2,b:t@ype} list_map2_fun {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: (a1, a2) -<fun,f> b):<f> list (b, n)
overload list_map2 with list_map2_fun

fun{a1,a2,b:t@ype} list_map2_cloptr {n:nat} {f:eff}
  (xs: list (a1, n), ys: list (a2, n), f: !(a1, a2) -<cloptr,f> b):<f> list (b, n)
overload list_map2 with list_map2_cloptr

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

fun{a:t@ype} list_tabulate {n:nat} {f:eff}
  (f: !natLt n -<f> a, n: int n):<f> list (a, n)

(* ****** ****** *)

fun{a:t@ype} list_tail {n:pos}
  (xs: list (a, n)):<> list (a, n-1)

fun{a:t@ype} list_tail_exn {n:nat}
  (xs: list (a, n)):<!exn> [n>0] list (a, n-1)

(* ****** ****** *)

fun{a,b:t@ype} list_zip {n:nat}
  (xs: list (a, n), ys: list (b, n)):<> list ('(a, b), n)

fun{a,b,c:t@ype} list_zip_with {n:nat} {f:eff}
  (xs: list (a, n), ys: list (b, n), f: !(a, b) -<cloptr,f> c)
  :<f> list (c, n)

fun{a1,a2:t@ype} list_unzip {n:nat}
  (xys: list ('(a1, a2), n)):<> (list (a1, n), list (a2, n))

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
