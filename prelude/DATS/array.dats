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

%{^

#include "prelude/CATS/array.cats"

%}

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

(* array pointers *)

(* ****** ****** *)

implement{a} atarray_get_elt_at (A, i) = A.[i]
implement{a} atarray_set_elt_at (A, i, x) = (A.[i] := x)

(* ****** ****** *)

implement{a} array_ptr_initialize_elt (A0, n0, x0) = let

fun aux {n:nat} {l:addr} .<n>.
  (pf: array_v (a?, n, l) | p: ptr l, n: int n, x0: a)
  :<> (array_v (a, n, l) | void) =
  if n > 0 then let
    prval (pf1, pf2) = array_v_uncons {a?} (pf)
    val () = !p := x0
    val (pf2 | ans) = aux (pf2 | p+sizeof<a>, n-1, x0)
  in
    (array_v_cons {a} (pf1, pf2) | ans)
  end else let
    prval () = array_v_unnil {a?} (pf)
  in
    (array_v_nil {a} () | ())
  end // end of [if]

val (pf | ()) = aux (view@ A0 | &A0, n0, x0)

in
  view@ A0 := pf
end // end of [array_ptr_initialize_elt]

(* ****** ****** *)

implement{a} array_ptr_initialize_lst (A0, n0, xs0) = let

fun aux {n:nat} {l:addr} .<n>.
  (pf: array_v (a?, n, l) | p: ptr l, n: int n, xs: list (a, n))
  :<> (array_v (a, n, l) | void) =
  if n > 0 then let
    prval (pf1, pf2) = array_v_uncons {a?} (pf)
    val+ list_cons (x, xs) = xs
    val () = !p := x
    val (pf2 | ans) = aux (pf2 | p+sizeof<a>, n-1, xs)
  in
    (array_v_cons {a} (pf1, pf2) | ans)
  end else let
    prval () = array_v_unnil {a?} pf
  in
    (array_v_nil {a} () | ())
  end

val (pf | ()) = aux (view@ A0 | &A0, n0, xs0)

in
  view@ A0 := pf
end // end of [array_ptr_initialize_lst]

(* ****** ****** *)

implement
  array_ptr_initialize_fun_tsz_cloptr
  {a} {n} {f} (base, asz, f, tsz) = let

  viewtypedef cloptr_t = (&(a?) >> a, natLt n) -<cloptr,f> void
  viewtypedef cloptr1_t = (!unit_v | &(a?) >> a, natLt n, !Ptr) -<cloptr,f> void
  prval () = coerce (f) where {
    extern fun coerce (f: !cloptr_t >> cloptr1_t):<> void
  }
  prval pf = unit_v ()
  val () = array_ptr_initialize_fun_tsz_mainclo
    {a} {unit_v} {Ptr} (pf | base, asz, f, tsz, null)
  prval unit_v () = pf
  prval () = coerce (f) where {
    extern fun coerce (f: !cloptr1_t >> cloptr_t):<> void
  }
in
  // empty
end // end of [array_ptr_initialize_fun_tsz_cloptr]

(* ****** ****** *)

implement{a} array_ptr_make_elt (n, x) = let
  val (pf_gc, pf | p) = array_ptr_alloc_tsz {a} (n, sizeof<a>)
  val () = array_ptr_initialize_elt<a> (!p, n, x)
in
  (pf_gc, pf | p)
end // end of [array_ptr_make_elt]

implement{a} array_ptr_make_lst (n, xs) = let
  val (pf_gc, pf | p) = array_ptr_alloc_tsz {a} (n, sizeof<a>)
  val () = array_ptr_initialize_lst<a> (!p, n, xs)
in
  (pf_gc, pf | p)
end // end of [array_ptr_make_lst]

(* ****** ****** *)

implement array_ptr_make_fun_tsz_cloptr {a} (asz, f, tsz) = let
  val (pf_gc, pf | p) = array_ptr_alloc_tsz {a} (asz, tsz)
  val () = array_ptr_initialize_fun_tsz_cloptr {a} (!p, asz, f, tsz)
in
  (pf_gc, pf | p)
end // end of [aray_ptr_make_fun_tsz_cloptr]

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

implement{a} array_ptr_get_elt_at (A, i) = A.[i]
implement{a} array_ptr_set_elt_at (A, i, x) = (A.[i] := x)

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

implement{a} array_make_elt (asz, x) = let
  val (pf_gc, pf | ptr) = array_ptr_make_elt<a> (asz, x)
  val (pfbox | ()) = vbox_make_view_ptr_gc (pf_gc, pf | ptr)
in
  @{ data= ptr, view= pfbox }
end // end of [array_make_elt]

implement array_make_fun_tsz_cloptr {a} (asz, f, tsz) = let
  val (pf_gc, pf_arr | p_arr) = array_ptr_alloc_tsz {a} (asz, tsz)
  val () = array_ptr_initialize_fun_tsz_cloptr {a} (!p_arr, asz, f, tsz)
  val (pfbox | ()) = vbox_make_view_ptr_gc (pf_gc, pf_arr | p_arr)
in
  @{ data= p_arr, view= pfbox }
end // end of [array_make_fun_tsz]

implement array_get_view_ptr (A) = @(A.view | A.data)

(* ****** ****** *)

implement{a} array_get_elt_at (A, i) = let
  val A_data = A.data; prval vbox pf = A.view in !A_data.[i]
end // end of [array_get_elt]

implement{a} array_set_elt_at (A, i, x) = let
  val A_data = A.data; prval vbox pf = A.view in !A_data.[i] := x
end // end of [array_set_elt_at]

implement{a} array_xch_elt_at (A, i, x) = let
  val A_data = A.data; prval vbox pf = A.view
in
  array_ptr_xch_elt_at<a> (!A_data, i, x)
end // end of [array_xch_elt_at]

(* ****** ****** *)

implement{a} array_exch (A, i1, i2) = begin
  if i1 <> i2 then let
    val A_data = A.data; prval vbox pf = A.view
  in
    array_ptr_exch<a> (!A_data, i1, i2)
  end
end // end of [array_exch]

(* ****** ****** *)

implement foreach_array_ptr_tsz_cloptr
  {a} {v} {n} {f} (pf | f, A, asz, tsz) = let
  viewtypedef cloptr_t = (!v | &a) -<cloptr,f> void
  fn app (pf: !v | x: &a, f: !cloptr_t):<f> void = f (pf | x)
  val () = foreach_array_ptr_tsz_main
    {a} {v} {cloptr_t} (pf | app, A, asz, tsz, f)
in
  // empty
end // end of [foreach_array_ptr_tsz_cloptr]

(* ****** ****** *)

implement
  iforeach_array_ptr_tsz_cloptr {a} {v} {n} {f} (pf | f, A, asz, tsz) = let
  viewtypedef cloptr_t = (!v | natLt n, &a) -<cloptr,f> void
  fn app (pf: !v | i: natLt n, x: &a, f: !cloptr_t):<f> void = f (pf | i, x)
  val () = iforeach_array_ptr_tsz_main
    {a} {v} {cloptr_t} (pf | app, A, asz, tsz, f)
in
  // empty
end // end of [iforeach_array_ptr_tsz_cloptr]

(* ****** ****** *)

implement{a} foreach_array_main
  {v} {vt} {n} {f} (pf | f, A, asz, env) = let
  typedef fun_t = (!v | a, !vt) -<f> void
  fun loop {i:nat | i <= n} .<n-i>. (
      pf: !v | f: fun_t, A: array (a, n), n: int n, i: int i, env: !vt
    ) :<f,!ref> void = begin
    if i < n then (f (pf | A[i], env); loop (pf | f, A, n, i+1, env)) else ()
  end // end of [loop]
in
  loop (pf | f, A, asz, 0, env)
end // end of [foreach_array_main]

implement{a}
  foreach_array_cloptr {v} {n} {f} (pf | f, A, asz) = let
  viewtypedef cloptr_t = (!v | a) -<cloptr,f> void
  fn app (pf: !v | x: a, f: !cloptr_t):<f> void = f (pf | x)
  val () = foreach_array_main<a> {v} {cloptr_t} (pf | app, A, asz, f)
in
  // empty
end // end of [foreach_array_cloptr]

implement{a}
  foreach_array_cloref {v} {n} {f} (pf | f, A, asz) = let
  viewtypedef cloref_t = (!v | a) -<cloref,f> void
  fn app (pf: !v | x: a, f: !cloref_t):<f> void = f (pf | x)
  val () = foreach_array_main<a> {v} {cloref_t} (pf | app, A, asz, f)
in
  // empty
end // end of [foreach_array_cloref]

(* ****** ****** *)

implement{a} iforeach_array_main
  {v} {vt} {n} {f} (pf | f, A, asz, env) = let
  viewtypedef fun_t = (!v | natLt n, a, !vt) -<fun,f> void
  fun loop {i:nat | i <= n} .<n-i>.
    (pf: !v | f: fun_t, A: array (a, n), n: int n, i: int i, env: !vt)
    :<f,!ref> void = begin
    if i < n then begin
      f (pf | i, A[i], env); loop (pf | f, A, n, i+1, env)
    end
  end // end of [loop]
  val () = loop (pf | f, A, asz, 0, env)
in
  // empty
end // end of [iforeach_array_main]

implement{a}
  iforeach_array_cloptr {v} {n} {f} (pf | f, A, asz) = let
  viewtypedef cloptr_t = (!v | natLt n, a) -<cloptr,f> void
  fn app (pf: !v | i: natLt n, x: a, f: !cloptr_t):<f> void = f (pf | i, x)
  val () = iforeach_array_main<a> {v} {cloptr_t} (pf | app, A, asz, f)
in
  // empty
end // end of [iforeach_array_cloptr]

implement{a}
  iforeach_array_cloref {v} {n} {f} (pf | f, A, asz) = let
  viewtypedef cloref_t = (!v | natLt n, a) -<cloref,f> void
  fn app (pf: !v | i: natLt n, x: a, f: !cloref_t):<f> void = f (pf | i, x)
  val () = iforeach_array_main<a> {v} {cloref_t} (pf | app, A, asz, f)
in
  // empty
end // end of [iforeach_array_cloref]

(* ****** ****** *)

// [array.sats] is already loaded by a call to [pervasive_load]
staload "prelude/SATS/array.sats" // this forces that the static
// loading function for [array.sats] is to be called at run-time

(* ****** ****** *)

%{$

ats_void_type
atspre_array_ptr_initialize_fun_tsz_main (
   ats_ptr_type A
 , ats_int_type asz
 , ats_ptr_type f
 , ats_int_type tsz
 , ats_ptr_type env
 ) {
  int i = 0;
  ats_ptr_type p = A ;
  while (i < asz) {
    ((ats_void_type (*)(ats_ptr_type, ats_int_type, ats_ptr_type))f)(p, i, env) ;
    p = (ats_ptr_type)(((char *)p) + tsz) ;
    ++i ;
  }
  return ;
}

ats_void_type
atspre_array_ptr_initialize_fun_tsz_mainclo (
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
    ++i ;
  }
  return ;
}

/* ****** ****** */

ats_void_type
atspre_foreach_array_ptr_tsz_main (
   ats_ptr_type f
 , ats_ptr_type A
 , ats_int_type asz
 , ats_int_type tsz
 , ats_ptr_type env
 ) {
  int i = 0;
  ats_ptr_type p = A ;
  while (i < asz) {
    ((ats_void_type (*)(ats_ptr_type, ats_ptr_type))f)(p, env) ;
    p = (ats_ptr_type)(((char *)p) + tsz) ;
    ++i ;
  }
  return ;
}

ats_void_type
atspre_iforeach_array_ptr_tsz_main (
   ats_ptr_type f
 , ats_ptr_type A
 , ats_int_type asz
 , ats_int_type tsz
 , ats_ptr_type env
 ) {
  int i = 0;
  ats_ptr_type p = A ;
  while (i < asz) {
    ((ats_void_type (*)(ats_int_type, ats_ptr_type, ats_ptr_type))f)(i, p, env) ;
    p = (ats_ptr_type)(((char *)p) + tsz) ;
    ++i ;
  }
  return ;
}

%}

(* ****** ****** *)

(* end of [array.dats] *)
