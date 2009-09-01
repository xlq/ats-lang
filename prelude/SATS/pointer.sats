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

// some common functions on pointers

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [pointer.sats] starts!\n"

#endif

(* ****** ****** *)

val null : ptr null = "atspre_null_ptr"

fun ptr_is_null {l:addr} (p: ptr l):<> bool (l == null)
  = "atspre_ptr_is_null"

fun ptr_is_not_null {l:addr} (p: ptr l):<> bool (l <> null)
  = "atspre_ptr_is_not_null"
overload ~ with ptr_is_not_null

(* ****** ****** *)

fun psucc {l:addr} (p: ptr l):<> ptr (l + 1)
  = "atspre_psucc"

and ppred {l:addr} (p: ptr l):<> ptr (l - 1)
  = "atspre_ppred"

overload succ with psucc
overload pred with ppred

(* ****** ****** *)

fun padd {l:addr} {i:int} (p: ptr l, i: size_t i):<> ptr (l + i)
  = "atspre_padd"

and psub {l:addr} {i:int} (p: ptr l, i: size_t i):<> ptr (l - i)
  = "atspre_psub"

fun pdiff {l1,l2:addr} (p1: ptr l1, p2: ptr l2):<> ptrdiff_t (l1 - l2)
  = "atspre_pdiff"

overload + with padd
overload - with psub
overload - with pdiff

fun plt {l1,l2:addr} (p1: ptr l1, p2: ptr l2):<> bool (l1 < l2)
  = "atspre_plt"

and plte {l1,l2:addr} (p1: ptr l1, p2: ptr l2):<> bool (l1 <= l2)
  = "atspre_plte"

and pgt {l1,l2:addr} (p1: ptr l1, p2: ptr l2):<> bool (l1 > l2)
  = "atspre_pgt"

and pgte {l1,l2:addr} (p1: ptr l1, p2: ptr l2):<> bool (l1 >= l2)
  = "atspre_pgte"

overload < with plt
overload <= with plte
overload > with pgt
overload >= with pgte

fun peq {l1,l2:addr} (p1: ptr l1, p2: ptr l2):<> bool (l1 == l2)
  = "atspre_peq"

and pneq {l1,l2:addr} (p1: ptr l1, p2: ptr l2):<> bool (l1 <> l2)
  = "atspre_pneq"

overload = with peq
overload <> with pneq

(* ****** ****** *)

fun compare_ptr_ptr
  (p1: ptr, p2: ptr):<> Sgn = "atspre_compare_ptr_ptr"
overload compare with compare_ptr_ptr

(* ****** ****** *)

// print functions for pointers

fun fprint_ptr {m:file_mode}
  (pf: file_mode_lte (m, w) | out: !FILE m, x: ptr):<!exnref> void
  = "atspre_fprint_ptr"

fun print_ptr (p: ptr):<!ref> void = "atspre_print_ptr"
and prerr_ptr (p: ptr):<!ref> void = "atspre_prerr_ptr"

overload fprint with fprint_ptr
overload print with print_ptr
overload prerr with prerr_ptr

// stringization

fun tostring_ptr (p: ptr):<> string = "atspre_tostring_ptr"
overload tostring with tostring_ptr

(* ****** ****** *)

praxi free_gc_viewt0ype_addr_trans
  {a1,a2:viewt@ype | sizeof a1 == sizeof a2} {l:addr}
  (pf_gc: !free_gc_v (a1, l) >> free_gc_v (a2, l)): void

(* ****** ****** *)

fun{a:viewt@ype} ptr_alloc ()
  :<> [l:addr | l > null] (free_gc_v (a, l), a? @ l | ptr l)

fun ptr_alloc_tsz {a:viewt@ype} (tsz: sizeof_t a)
  :<> [l:addr | l > null] (free_gc_v (a, l), a? @ l | ptr l)
  = "atspre_ptr_alloc_tsz"

fun ptr_free {a:viewt@ype} {l:addr}
  (_: free_gc_v (a, l), _: a? @ l | _: ptr l):<> void
  = "atspre_ptr_free"

(* ****** ****** *)

// template
fun{a:t@ype} ptr_get_t_main {v:view} {l:addr}
  (pf1: !v, pf2: vcontain_p (v, a @ l) | p: ptr l):<> a

// implemented in [prelude/DATS/pointer.dats]
fun{a:t@ype} ptr_get_t {l:addr} (pf: !a @ l | p: ptr l):<> a

// implemented in [prelude/DATS/pointer.dats]
fun{a:t@ype} ptr_set_t {l:addr}
  (pf: !(a?) @ l >> a @ l | p: ptr l, x: a):<> void

(* ****** ****** *)

// template
fun{a:t@ype} ptr_move_t_main {v:view} {l1,l2:addr}
  (pf1: !v, pf2: vcontain_p (v, a @ l1), pf3: !(a?) @ l2 >> a @ l2 |
   p1: ptr l1, p2: ptr l2)
  :<> void

// implemented in [prelude/DATS/pointer.dats]
fun{a:t@ype} ptr_move_t {l1,l2:addr}
  (pf1: !a @ l1, pf2: !(a?) @ l2 >> a @ l2 | p1: ptr l1, p2: ptr l2):<> void

// implemented in [prelude/CATS/pointer.cats]
fun ptr_move_t_tsz {a:t@ype} {l1,l2:addr} (
    pf1: !a @ l1, pf2: !(a?) @ l2 >> a @ l2
  | p1: ptr l1, p2: ptr l2, tsz: sizeof_t a
  ) :<> void
  = "atspre_ptr_move_tsz"

(* ****** ****** *)

// implemented in [prelude/DATS/pointer.dats]
fun{a:viewt@ype} ptr_get_vt {l:addr}
  (pf: !a @ l >> (a?) @ l | p: ptr l):<> a

// implemented in [prelude/DATS/pointer.dats]
fun{a:viewt@ype} ptr_set_vt {l:addr}
  (pf: !(a?) @ l >> a @ l | p: ptr l, x: a):<> void

(* ****** ****** *)

// implemented in [prelude/DATS/pointer.dats]
fun{a:viewt@ype} ptr_move_vt {l1,l2:addr} (
    pf1: !a @ l1 >> (a?) @ l1, pf2: !(a?) @ l2 >> a @ l2
  | p1: ptr l1, p2: ptr l2
  ) :<> void

// implemented in [prelude/CATS/pointer.cats]
fun ptr_move_vt_tsz {a:viewt@ype} {l1,l2:addr} (
    pf1: !a @ l1 >> (a?) @ l1, pf2: !(a?) @ l2 >> a @ l2
  | p: ptr l1, p2: ptr l2, tsz: sizeof_t a
  ) :<> void
  = "atspre_ptr_move_tsz"

(* ****** ****** *)

// implemented in [prelude/DATS/pointer.dats]
fun{a:t@ype} ptr_get_inv {l:addr} (pf: !a @ l | p: ptr l):<> a

// implemented in [prelude/DATS/pointer.dats]
fun{a:t@ype} ptr_set_inv {l:addr} (pf: !a @ l | p: ptr l, x: a):<> void

(* ****** ****** *)

(*

// two axioms declared in [prelude/SATS/memory.sats]
praxi ptr_to_bytearr : {a:viewtype} {l:addr} a? @ l -<prf> bytearr_v (sizeof a, l)
praxi ptr_of_bytearr : {a:viewtype} {l:addr} bytearr_v (sizeof a, l) -<prf> a? @ l

*)

prfun ptr_view_conversion
  {a1,a2:viewt@ype | sizeof a1 == sizeof a2} {l:addr}
  (pf: !a1? @ l >> a2? @ l):<prf> void

(* ****** ****** *)

(*

// This should be moved to another place as it is not supported by
// ATS/Geizella

fun{a:t@ype} ptr_get_read
  {v:view} {l:addr} (pf1: !v, pf2: r@ead (v, a @ l) | p: ptr l):<> a

*)

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [pointer.sats] finishes!\n"

#endif

(* end of [pointer.sats] *)
