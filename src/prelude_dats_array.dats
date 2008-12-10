(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
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

%{^

#include "prelude/CATS/array.cats"

%}

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

(* array pointers *)

(* ****** ****** *)

implement array_ptr_initialize_cloptr_tsz {a} {n} {f}
  (base, asz, f, tsz) = let

  viewtypedef cloptr_t = (&(a?) >> a, natLt n) -<cloptr,f> void
  viewtypedef cloptr1_t = (!unit_v | &(a?) >> a, natLt n, !Ptr) -<cloptr,f> void
  prval () = coerce (f) where {
    extern fun coerce (f: !cloptr_t >> cloptr1_t):<> void
  }
  prval pf = unit_v ()
  val () = array_ptr_initialize_cloptr_tsz_main
    {a} {unit_v} {Ptr} (pf | base, asz, f, tsz, null)
  prval unit_v () = pf
  prval () = coerce (f) where {
    extern fun coerce (f: !cloptr1_t >> cloptr_t):<> void
  }
in
  // empty
end

(* ****** ****** *)

implement array_ptr_takeout2_tsz
  {a} {n, i1, i2} {l0} (pf | A, i1, i2, tsz) = let
  val [off1: int] (pf1_mul | off1) = i1 imul2 tsz
  val [off2: int] (pf2_mul | off2) = i2 imul2 tsz
  prval (pf1, pf2, fpf) = array_v_takeout2 {a} (pf1_mul, pf2_mul, pf)
in
  #[ l0+off1, l0+off2 | (pf1, pf2, fpf | A+off1, A+off2) ]
end // end of [array_ptr_takeout2_tsz]

(* ****** ****** *)

(* persistent arrays *)

(* ****** ****** *)

assume array_viewt0ype_int_type
  (a:viewt@ype, n:int) = [l:addr] @{
  data= ptr l, view= vbox (array_v (a, n, l))
} // end of [array_viewt0ype_int_type]

(*

viewtypedef
arraysize_viewt0ype_int_viewt0ype (a: viewt@ype, n:int) =
  [l:addr | l <> null] (free_gc_v l, @[a][n] @ l | ptr l, int n)

*)

implement array_make_arraysize (x) = let
  val (pfbox | ()) = vbox_make_view_ptr_gc (x.0, x.1 | x.2)
in
  @{ data= x.2, view= pfbox }
end // end of [array]

//

implement array_make_cloptr_tsz {a} (asz, f, tsz) = let
  val (pf_gc, pf_arr | p_arr) = array_ptr_alloc_tsz {a} (asz, tsz)
  val () = array_ptr_initialize_cloptr_tsz {a} (!p_arr, asz, f, tsz)
  val (pfbox | ()) = vbox_make_view_ptr_gc (pf_gc, pf_arr | p_arr)
in
  @{ data= p_arr, view= pfbox }
end // end of [array_make_cloptr_tsz]

implement array_get_view_ptr (A) = @(A.view | A.data)

(* ****** ****** *)

%{$

ats_void_type
atspre_array_ptr_initialize_cloptr_tsz_main (
   ats_ptr_type A
 , ats_int_type asz
 , ats_ptr_type f
 , ats_int_type tsz
 , ats_ptr_type env
 ) {
  int i = 0;
  ats_ptr_type p = A ;
  while (i < asz) {
    ((ats_void_type (*)(ats_clo_ptr_type, ats_ptr_type, ats_int_type, ats_ptr_type))ats_closure_fun(f))(f, p, i, env) ;
    p = (ats_ptr_type)(((char *)p) + tsz) ;
    i += 1 ;
  }
  return ;
}

%}

(* ****** ****** *)

(* end of [prelude_dats_array.dats] *)
