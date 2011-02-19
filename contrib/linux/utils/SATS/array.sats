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
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)
// Start Time: February, 2011
//
(* ****** ****** *)

staload "contrib/linux/basics.sats"

(* ****** ****** *)

fun{a:t@ype}
array_ptr_get_elt_at {n:int}
  {i:nat | i < n} (A: &(@[a][n]), i: size_t i):<> a
overload [] with array_ptr_get_elt_at

fun{a:t@ype}
array_ptr_set_elt_at {n:int}
  {i:nat | i < n} (A: &(@[a][n]), i: size_t i, x: a):<> void
overload [] with array_ptr_set_elt_at

fun{a:viewt@ype}
array_ptr_xch_elt_at {n:int}
  {i:nat | i < n} {l:addr} (A: &(@[a][n]), i: size_t i, x: &a):<> void
// end of [array_ptr_xch_elt_at]

(* ****** ****** *)
//
// HX: these functions are present mostly for convenience as
// a programmer ofter uses values of the type int as array indices:
//
fun{a:t@ype}
array_ptr_get_elt_at__intsz
  {n:int} {i:nat | i < n} (A: &(@[a][n]), i: int i):<> a
overload [] with array_ptr_get_elt_at__intsz

fun{a:t@ype}
array_ptr_set_elt_at__intsz
  {n:int} {i:nat | i < n} (A: &(@[a][n]), i: int i, x:a):<> void
overload [] with array_ptr_set_elt_at__intsz

fun{a:viewt@ype}
array_ptr_xch_elt_at__intsz {n:int}
  {i:nat | i < n} {l:addr} (A: &(@[a][n]), i: int i, x: &a):<> void
// end of [array_ptr_xch_elt_at__intsz]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_kalloc {n:nat}
  (asz: size_t n):<> [l:agz] (kfree_v (a, n, l), array_v (a?, n, l) | ptr l)
// end of [array_ptr_kalloc]

(*
// implemented in C
*)
fun array_ptr_kalloc_tsz
  {a:viewt@ype} {n:nat} (
  asz: size_t n, tsz: sizeof_t a
) :<> [l:agz] (kfree_v (a, n, l), array_v (a?, n, l) | ptr l)
  = "atsctrb_linux_array_ptr_kalloc_tsz"
// end of [array_ptr_kalloc_tsz]

(* ****** ****** *)

(*
// implemented in C
*)
fun array_ptr_kfree
  {a:viewt@ype} {n:int} {l:addr} (
  pf_gc: kfree_v (a, n, l), pf_arr: array_v (a?, n, l) | p_arr: ptr l
) :<> void = "atsctrb_linux_array_ptr_kfree"

(* ****** ****** *)

fun{a:t@ype}
array_ptr_initialize_elt {n:nat} (
  base: &(@[a?][n]) >> @[a][n], asz: size_t n, ini: a
) :<> void // end of [array_ptr_initialize_elt]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_initialize_fun
  {v:view} {n:nat} (
  pf: !v
| base: &(@[a?][n]) >> @[a][n]
, asz: size_t n
, f: (!v | sizeLt n, &(a?) >> a) -<fun> void
) :<> void // end of [array_ptr_initialize_fun]

fun{a:viewt@ype}
array_ptr_initialize_clo
  {v:view} {n:nat} (
  pf: !v 
| base: &(@[a?][n]) >> @[a][n]
, asz: size_t n
, f: &(!v | sizeLt n, &(a?) >> a) -<clo> void
) :<> void // end of [array_ptr_initialize_clo]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_clear_fun
  {v:view} {n:nat} (
  pf: !v
| base: &(@[a][n]) >> @[a?][n]
, asz: size_t n
, f: (!v | &a >> a?) -<fun> void
) :<> void // end of [array_ptr_clear_fun]

fun{a:viewt@ype}
array_ptr_clear_clo
  {v:view} {n:nat} (
  pf: !v
| base: &(@[a][n]) >> @[a?][n]
, asz: size_t n
, f: &(!v | &a >> a?) -<clo> void
) :<> void // end of [array_ptr_clear_clo]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_split
  {n:int} {i:nat | i <= n} {l0:addr} (
  pf: array_v (a, n, l0) | base: ptr l0, offset: size_t i
) :<> [ofs:nat] (
  MUL (i, sizeof(a), ofs)
, array_v (a, i, l0), array_v (a, n-i, l0+ofs)
| ptr (l0+ofs)
) // end of [array_ptr_split]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_takeout
  {n:int} {i:nat | i < n} {l0:addr} (
  pf: array_v (a, n, l0) | base: ptr l0, offset: size_t i
) :<> [l:addr] (
  a @ l
, a @ l -<lin,prf> array_v (a, n, l0)
| ptr l
) // end of [array_ptr_takeout]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_takeout2 {n:int}
  {i1,i2:nat | i1 < n; i2 < n; i1 <> i2} {l0:addr} (
  pf: array_v (a, n, l0)
| base: ptr l0
, off1: size_t i1, off2: size_t i2
) :<> [l1,l2:addr] (
  a @ l1
, a @ l2, (a @ l1, a @ l2) -<lin,prf> array_v (a, n, l0)
| ptr l1
, ptr l2
) // end of [array_ptr_takeout2]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_exch
  {n:int} {i1,i2:nat | i1 < n; i2 < n; i1 <> i2}
  (A: &(@[a][n]), i1: size_t i1, i2: size_t i2):<> void
// end of [array_ptr_exch]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_foreach_fun {v:view} {n:nat} (
  pf: !v
| base: &(@[a][n]), f: (!v | &a) -<fun> void, asz: size_t n
) :<> void // end of [array_ptr_foreach_fun]

fun{a:viewt@ype}
array_ptr_foreach_clo {v:view} {n:nat} (
  pf: !v
| base: &(@[a][n]), f: &(!v | &a) -<clo> void, asz: size_t n
) :<> void // end of [array_ptr_foreach_clo]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_iforeach_fun {v:view} {n:nat} (
  pf: !v
| base: &(@[a][n]), f: (!v | sizeLt n, &a) -<fun> void, asz: size_t n
) :<> void // end of [array_ptr_iforeach_fun]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_iforeach_clo {v:view} {n:nat} (
  pf: !v
| base: &(@[a][n]), f: &(!v | sizeLt n, &a) -<clo> void, asz: size_t n
) :<> void // end of [array_ptr_iforeach_clo]

(* ****** ****** *)

(* end of [array.sats] *)
