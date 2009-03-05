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

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

#define i2sz size1_of_int1

(* ****** ****** *)

// array0 implementation

(* ****** ****** *)

assume array0_viewt0ype_type
  (a:viewt@ype) = [n:nat] [l:addr] '{
  data= ptr l, size= size_t n, view= vbox (array_v (a, n, l))
} // end of [array0_viewt0ype_type]

(* ****** ****** *)

implement array0_make_arraysize {a} {n} (arrsz) = let
  prval () = free_gc_elim {a} (arrsz.0)
  val (pfbox | ()) = vbox_make_view_ptr (arrsz.1 | arrsz.2)
in '{
  data= arrsz.2, size= i2sz arrsz.3, view= pfbox
} end // end of [array0_make_arraysize]

(* ****** ****** *)

implement{a} array0_make_elt (asz, x) = let
  val asz = size1_of_size asz
in
  if asz >= 0 then let
    val A = array_make_elt<a> (asz, x)
    val (A_view | A_data) = array_get_view_ptr (A)
  in '{
    data= A_data, size= asz, view= A_view
  } end else begin
    exit_errmsg (1, "Exit: [array0_make]: negative array size\n")
  end // end of [if]
end // end of [array0_make_elt]

(* ****** ****** *)

implement array0_size (A) = A.size

(* ****** ****** *)

implement{a} array0_get_elt_at_exn (A, i) = let
  val i = size1_of_size i
  val A_data = A.data; val asz = A.size
in
  if i < asz then let
    prval vbox pf = A.view in !A_data.[i]
  end else begin
    $raise SubscriptException
  end // end of [if]
end (* end of [array0_get_elt_at_exn] *)

implement{a} array0_set_elt_at_exn (A, i, x) = let
  val i = size1_of_size i
  val A_data = A.data; val asz = A.size
in
  if i < asz then let
    prval vbox pf = A.view in !A_data.[i] := x
  end else begin
    $raise SubscriptException
  end
end (* end of [array0_set_elt_at_exn] *)

(* ****** ****** *)

implement{a} array0_get_elt_at_exn__isz (A, i) = let
  val i = int1_of_int i
in
  if i >= 0 then begin
    array0_get_elt_at_exn<a> (A, i2sz i)
  end else begin
    $raise SubscriptException
  end // end of [if]
end (* end of [array0_get_elt_at_exn__isz] *)
  
implement{a} array0_set_elt_at_exn__isz (A, i, x) = let
  val i = int1_of_int i
in
  if i >= 0 then begin
    array0_set_elt_at_exn<a> (A, i2sz i, x)
  end else begin
    $raise SubscriptException
  end // end of [if]
end (* end of [array0_set_elt_at_exn__isz] *)
  
(* ****** ****** *)

// [array0.sats] is already loaded by a call to [pervasive_load]
staload _(*anonymous*) = "prelude/SATS/array0.sats" // this forces that the static
// loading function for [array0.sats] is to be called at run-time
// this is really needed only if some datatypes are declared in [array0.sats]

(* ****** ****** *)

(* end of [array0.dats] *)
