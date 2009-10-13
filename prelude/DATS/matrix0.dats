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
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
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

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

#define i2sz size1_of_int1

(* ****** ****** *)

// matrix0 implementation

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

assume matrix0_viewt0ype_type (a:viewt@ype) = ref [l:addr] [m,n:nat] [mn:int] (
  MUL (m, n, mn), free_gc_v (a, mn, l), @[a][mn] @ l | ptr l, size_t m, size_t n
) // end of [matrix0_viewt0ype_type]

(* ****** ****** *)

implement matrix0_make_arraysize
  {a} {m,n} {mn} (pf_mul | m, n, arrsz) = let
in
  ref @(pf_mul, arrsz.0, arrsz.1 | arrsz.2, m, n)
end (* end of [matrix0_make_arraysize] *)

(* ****** ****** *)

implement{a} matrix0_make_elt (row, col, x0) = let
  val [m:int] row = size1_of_size (row)
  val [n:int] col = size1_of_size (col)
  val [mn:int] (pf_mul | asz) = mul2_size1_size1 (row, col)
  prval () = mul_nat_nat_nat (pf_mul)
  val tsz = sizeof<a>
  val (pf_gc, pf_arr | p_arr) = array_ptr_alloc_tsz {a} (asz, tsz)
  var ini: a = x0
  val () = array_ptr_initialize_elt_tsz {a} (!p_arr, asz, ini, tsz)
in
  matrix0_make_arraysize {a} {m,n} {mn} (pf_mul | row, col, @(pf_gc, pf_arr | p_arr, asz))
end // end of [matrix0_make_elt]

(* ****** ****** *)

implement matrix0_row (M) = let
  val (vbox pf | p) = ref_get_view_ptr (M) in p->4
end // end of [matrix0_row]

implement matrix0_col (M) = let
  val (vbox pf | p) = ref_get_view_ptr (M) in p->5
end // end of [matrix0_col]

(* ****** ****** *)

// this one is proven in [matrix.dats]
extern prfun lemma_for_matrix_subscripting
  {m,n:nat} {i:nat | i < m} {mn,p:int}
  (pf1: MUL (m, n, mn), pf2: MUL (i, n, p)): [p+n <= mn] void
// end of [lemma_for_matrix_subscripting]  

implement{a} matrix0_get_elt_at (M, i, j) = let
  val (vbox pf | p) = ref_get_view_ptr (M)
  val i = size1_of_size i
  val j = size1_of_size j
  val p_data = p->3; val row = p->4 and col = p->5
in
  if i < row then (
    if j < col then let
      prval pf_data = p->2
      val (pf_mul | icol) = mul2_size1_size1 (i, col)
      prval () = lemma_for_matrix_subscripting (p->0, pf_mul)
      prval () = mul_nat_nat_nat (pf_mul) 
      val x = p_data->[icol + j]
      prval () = p->2 := pf_data
    in
      x // return value
    end else begin
      $raise MatrixSubscriptException ()
    end (* end of [if] *)
  ) else (
    $raise MatrixSubscriptException () // out-of-row
  ) // end of [if]
end (* end of [matrix0_get_elt_at] *)

implement{a} matrix0_set_elt_at (M, i, j, x) = let
  val (vbox pf | p) = ref_get_view_ptr (M)
  val i = size1_of_size i
  val j = size1_of_size j
  val p_data = p->3; val row = p->4 and col = p->5
in
  if i < row then (
    if j < col then let
      prval pf_data = p->2
      val (pf_mul | icol) = mul2_size1_size1 (i, col)
      prval () = lemma_for_matrix_subscripting (p->0, pf_mul)
      prval () = mul_nat_nat_nat (pf_mul) 
      val () = p_data->[icol + j] := x
      prval () = p->2 := pf_data
    in
      // nothing
    end else begin
      $raise MatrixSubscriptException ()
    end (* end of [if] *)
  ) else (
    $raise MatrixSubscriptException () // out-of-row
  ) // end of [if]
end (* end of [matrix0_set_elt_at] *)

(* ****** ****** *)

implement{a}
  matrix0_get_elt_at__intsz (A, i, j) = let
  val i = int1_of_int i and j = int1_of_int j in
  if i >= 0 then begin
    if j >= 0 then begin
      matrix0_get_elt_at<a> (A, i2sz i, i2sz j)
    end else begin
      $raise MatrixSubscriptException ()
    end (* end of [if] *)
  end else begin
    $raise MatrixSubscriptException () // out-of-row
  end // end of [if]
end (* end of [matrix0_get_elt_at__intsz] *)

implement{a}
  matrix0_set_elt_at__intsz (A, i, j, x) = let
  val i = int1_of_int i and j = int1_of_int j in
  if i >= 0 then begin
    if j >= 0 then begin
      matrix0_set_elt_at<a> (A, i2sz i, i2sz j, x)
    end else begin
      $raise MatrixSubscriptException ()
    end (* end of [if] *)
  end else begin
    $raise MatrixSubscriptException () // out-of-row
  end // end of [if]
end (* end of [matrix0_set_elt_at__intsz] *)

(* ****** ****** *)

// [matrix0.sats] is already loaded by a call to [pervasive_load]
staload _(*anonymous*) = "prelude/SATS/matrix0.sats" // this forces that the static
// loading function for [matrix0.sats] is to be called at run-time
// this is really needed only if some datatypes are declared in [matrix0.sats]

(* ****** ****** *)

(* end of [matrix0.dats] *)
