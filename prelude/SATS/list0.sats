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

(* 
** HX:
** Note that the functions declared in this file are for supporting list
** processing in ML-like manner. Many more functions are available in the
** following file:
**
** $ATSHOME/libats/smlbas/SATS/list.sats
**
** that are implemented for the same purpose.
*)

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [list0.sats] starts!\n"

#endif

(* ****** ****** *)

// for forming singleton lists
// macdef list0_sing (x) = list0_cons (,(x), list0_nil ())

(* ****** ****** *)

// a casting function implemented in [prelude/CATS/list.cats]
castfn list0_of_list1 {a:t@ype} (xs: List a):<> list0 a
  = "atspre_list0_of_list1"

// a casting function implemented in [prelude/CATS/list.cats]
castfn list0_of_list_vt {a:t@ype} (xs: List_vt a):<> list0 a
  = "atspre_list0_of_list_vt"

// a casting function implemented in [prelude/DATS/list.cats]
castfn list1_of_list0 {a:t@ype} (xs: list0 a):<> List a
  = "atspre_list1_of_list0"

(* ****** ****** *)

fun{a:t@ype}
list0_make_arrsz
  {n:nat} (arrsz: arraysize (a, n)):<> list0 a
// end of [list0_make_arrsz]

(* ****** ****** *)

fun{a:t@ype} list0_append (xs: list0 a, ys: list0 a):<> list0 a
overload + with list0_append

(* ****** ****** *)

fun{a:t@ype} list0_concat (xs: list0 (list0 a)):<> list0 a

(* ****** ****** *)

fun{a:t@ype} list0_exists_fun (xs: list0 a, f: a -<fun1> bool): bool
fun{a:t@ype} list0_exists_cloref (xs: list0 a, f: a -<cloref1> bool): bool

(* ****** ****** *)

fun{a:t@ype} list0_filter_fun (xs: list0 a, pred: a -<fun1> bool): list0 a
fun{a:t@ype} list0_filter_cloref (xs: list0 a, pred: a -<cloref1> bool): list0 a

(* ****** ****** *)

fun{init,a:t@ype}
list0_fold_left {f:eff}
  (f: (init, a) -<cloref,f> init, ini: init, xs: list0 a):<f> init

fun{a,sink:t@ype}
list0_fold_right {f:eff}
  (f: (a, sink) -<cloref,f> sink, xs: list0 a, snk: sink):<f> sink

(* ****** ****** *)

fun{a:t@ype} list0_forall_fun (xs: list0 a, f: a -<fun1> bool): bool
fun{a:t@ype} list0_forall_cloref (xs: list0 a, f: a -<cloref1> bool): bool

(* ****** ****** *)

fun{a:t@ype} list0_foreach_fun (xs: list0 a, f: a -<fun1> void): void
fun{a:t@ype} list0_foreach_cloref (xs: list0 a, f: a -<cloref1> void): void

(* ****** ****** *)

fun{a:t@ype} list0_head_exn (xs: list0 a): a

(* ****** ****** *)

fun{a:t@ype} list0_length (xs: list0 a):<> int

(* ****** ****** *)

fun{a,b:t@ype} list0_map_fun (xs: list0 a, f: a -<fun1> b): list0 b
fun{a,b:t@ype} list0_map_cloref (xs: list0 a, f: a -<cloref1> b): list0 b

(* ****** ****** *)

fun{a1,a2,b:t@ype} list0_map2_fun
  (xs1: list0 a1, xs2: list0 a2, f: (a1, a2) -<fun1> b): list0 b
fun{a1,a2,b:t@ype} list0_map2_cloref
  (xs1: list0 a1, xs2: list0 a2, f: (a1, a2) -<cloref1> b): list0 b

(* ****** ****** *)

fun{a:t@ype} list0_nth_exn (xs: list0 a, i: int): a
fun{a:t@ype} list0_nth_opt (xs: list0 a, i: int): Option a

(* ****** ****** *)

fun{a:t@ype} list0_reverse (xs: list0 a): list0 a
fun{a:t@ype} list0_reverse_append (xs: list0 a, ys: list0 a): list0 a
(*
fun{a:t@ype} list0_revapp (xs: list0 a, ys: list0 a): list0 a
*)

(* ****** ****** *)

fun{a:t@ype} list0_tail_exn (xs: list0 a): list0 a

(* ****** ****** *)

fun{a:t@ype} list0_take_exn (xs: list0 a, n: int): list0 a
fun{a:t@ype} list0_drop_exn (xs: list0 a, n: int): list0 a

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [list0.sats] finishes!\n"

#endif

(* end of [list0.sats] *)
