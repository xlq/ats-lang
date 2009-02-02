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

#define i2sz size1_of_int1

(* ****** ****** *)

(* array pointers *)

(* ****** ****** *)

implement{a} array_ptr_get_elt_at (A, i) = A.[i]
implement{a} array_ptr_set_elt_at (A, i, x) = (A.[i] := x)

implement{a} array_ptr_xch_elt_at (A, i, x) = let
  var tmp: a // uninitialized
  val (pf, fpf | p) = array_ptr_takeout_tsz (view@ A | &A, i, sizeof<a>)
  val () = (tmp := !p; !p := x); prval () = view@ A := fpf pf
in
  x := tmp
end // end of [array_ptr_xch_elt_at]

(* ****** ****** *)

//
// These functions are present solely for notational convenience:
//

implement{a} array_ptr_get_elt_at__intsz
  (A, i) = let val i = i2sz i in A.[i] end

implement{a} array_ptr_set_elt_at__intsz
  (A, i, x) = let val i = i2sz i in A.[i] := x end

implement{a} array_ptr_xch_elt_at__intsz (A, i, x) = let
  val i = i2sz i in array_ptr_xch_elt_at<a> (A, i, x)
end // end of [array_ptr_xch_elt_at__intsz]

(* ****** ****** *)

implement{a} array_ptr_alloc (n) =
  array_ptr_alloc_tsz {a} (n, sizeof<a>)

(* ****** ****** *)

implement{a} array_ptr_initialize_elt (A0, n0, x0) = let

fun aux {n:nat} {l:addr} .<n>.
  (pf: array_v (a?, n, l) | p: ptr l, n: size_t n, x0: a)
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
  (pf: array_v (a?, n, l) | p: ptr l, n: size_t n, xs: list (a, n))
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

implement array_ptr_initialize_fun_tsz
  {a} {n} {f} (base, asz, f, tsz) = let

  typedef funptr_t = (&(a?) >> a, sizeLt n) -<f> void
  typedef funptr1_t = (!unit_v | &(a?) >> a, sizeLt n, !Ptr) -<f> void
  val f1 = coerce (f) where {
    extern fun coerce (f: funptr_t):<> funptr1_t = "atspre_fun_coerce"
  }
  prval pf = unit_v ()
  val () = array_ptr_initialize_fun_tsz_main
    {a} {unit_v} {Ptr} (pf | base, asz, f1, tsz, null)
  prval unit_v () = pf
in
  // empty
end // end of [array_ptr_initialize_fun_tsz]

(* ****** ****** *)

implement array_ptr_initialize_clo_tsz
  {a} {n} {f} (base, asz, f, tsz) = let

  val p_f = &f; prval pf_f = view@ f
  viewtypedef clo_t = (&(a?) >> a, sizeLt n) -<clo,f> void
  viewtypedef clo1_t = (!unit_v | &(a?) >> a, sizeLt n, !Ptr) -<clo,f> void
  prval pf1_f = coerce (pf_f) where {
    extern prfun coerce {l:addr} (pf: clo_t @ l): clo1_t @ l
  }
  prval pf = unit_v ()
  val () = array_ptr_initialize_clo_tsz_main
    {a} {unit_v} {Ptr} (pf | base, asz, !p_f, tsz, null)
  prval unit_v () = pf
  prval pf_f = coerce (pf1_f) where {
    extern prfun coerce {l:addr} (pf: clo1_t @ l): clo_t @ l
  }
  prval () = view@ f := pf_f
in
  // empty
end // end of [array_ptr_initialize_clo_tsz]

(* ****** ****** *)

implement{a} array_ptr_takeout (pf | A, i) =
  array_ptr_takeout_tsz {a} (pf | A, i, sizeof<a> )
// end of [array_ptr_takeout]

(* ****** ****** *)

infixl ( * ) szmul2

implement{a} array_ptr_takeout2 (pf | A, i1, i2) =
  array_ptr_takeout2_tsz {a} (pf | A, i1, i2, sizeof<a> )
// end of [array_ptr_takeout2]

implement array_ptr_takeout2_tsz
  {a} {n, i1, i2} {l0} (pf | A, i1, i2, tsz) = let
  val [off1:int] (pf1_mul | off1) = i1 szmul2 tsz
  val [off2:int] (pf2_mul | off2) = i2 szmul2 tsz
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

implement array_make_arraysize {a} {n} (arrsz) = let
  prval () = free_gc_elim {a} (arrsz.0) // return the certificate
  val (pfbox | ()) = vbox_make_view_ptr (arrsz.1 | arrsz.2)
in
  @{ data= arrsz.2, view= pfbox }
end // end of [array]

//

implement{a} array_make_elt (asz, x) = let
  val (pf_gc, pf_arr | p_arr) = array_ptr_alloc_tsz {a} (asz, sizeof<a>)
  prval () = free_gc_elim {a} (pf_gc) // return the certificate
  val () = array_ptr_initialize_elt<a> (!p_arr, asz, x)
  val (pfbox | ()) = vbox_make_view_ptr (pf_arr | p_arr)
in
  @{ data= p_arr, view= pfbox }
end // end of [array_make_elt]

implement array_make_clo_tsz {a} (asz, f, tsz) = let
  val (pf_gc, pf_arr | p_arr) = array_ptr_alloc_tsz {a} (asz, tsz)
  prval () = free_gc_elim {a} (pf_gc) // return the certificate
  val () = array_ptr_initialize_clo_tsz {a} (!p_arr, asz, f, tsz)
  val (pfbox | ()) = vbox_make_view_ptr (pf_arr | p_arr)
in
  @{ data= p_arr, view= pfbox }
end // end of [array_make_clo_tsz]

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

implement{a} array_get_elt_at__intsz (A, i) = let
  val i = i2sz i; val A_data = A.data; prval vbox pf = A.view
in
  !A_data.[i]
end // end of [array_get_elt]

implement{a} array_set_elt_at__intsz (A, i, x) = let
  val i = i2sz i; val A_data = A.data; prval vbox pf = A.view
in
  !A_data.[i] := x
end // end of [array_set_elt_at]

implement{a} array_xch_elt_at__intsz (A, i, x) = let
  val i = i2sz i; val A_data = A.data; prval vbox pf = A.view
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

implement foreach_array_ptr_tsz_clo
  {a} {v} {n} {f} (pf_v | f, A, asz, tsz) = let
  viewtypedef clo_t = (!v | &a) -<clo,f> void
  stavar l_f: addr
  val p_f: ptr l_f = &f
  viewdef V = @(v, clo_t @ l_f)
  fn app (pf: !V | x: &a, p_f: !ptr l_f):<f> void = let
    prval (pf1, pf2) = pf; val () = !p_f (pf1 | x) in pf := (pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = foreach_array_ptr_tsz_main
    {a} {V} {ptr l_f} (pf | app, A, asz, tsz, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [foreach_array_ptr_tsz_clo]

(* ****** ****** *)

implement
  iforeach_array_ptr_tsz_clo {a} {v} {n} {f} (pf_v | f, A, asz, tsz) = let
  viewtypedef clo_t = (!v | sizeLt n, &a) -<clo,f> void
  stavar l_f: addr
  val p_f: ptr l_f = &f
  viewdef V = @(v, clo_t @ l_f)
  fn app (pf: !V | i: sizeLt n, x: &a, p_f: !ptr l_f):<f> void = let
    prval (pf1, pf2) = pf; val () = !p_f (pf1 | i, x) in pf := (pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = iforeach_array_ptr_tsz_main
    {a} {V} {ptr l_f} (pf | app, A, asz, tsz, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [iforeach_array_ptr_tsz_clo]

(* ****** ****** *)

implement{a} foreach_array_main
  {v} {vt} {n} {f} (pf | f, A, asz, env) = let
  typedef fun_t = (!v | a, !vt) -<f> void
  fun loop {i:nat | i <= n} .<n-i>. (
      pf: !v
    | f: fun_t, A: array (a, n), n: size_t n, i: size_t i, env: !vt
    ) :<f,!ref> void = begin
    if i < n then (f (pf | A[i], env); loop (pf | f, A, n, i+1, env)) else ()
  end // end of [loop]
in
  loop (pf | f, A, asz, 0, env)
end // end of [foreach_array_main]

implement{a} foreach_array_clo
  {v} {n} {f} (pf_v | f, A, asz) = let
  stavar l_f: addr
  typedef clo_t = (!v | a) -<clo,f> void
  val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x: a, p_f: !ptr l_f):<f> void = let
    prval (pf1, pf2) = pf in !p_f (pf1 | x); pf := (pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = foreach_array_main<a> {V} {ptr l_f} (pf | app, A, asz, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [foreach_array_clo]

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
  viewtypedef fun_t = (!v | sizeLt n, a, !vt) -<fun,f> void
  fun loop {i:nat | i <= n} .<n-i>. (
      pf: !v
    | f: fun_t, A: array (a, n), n: size_t n, i: size_t i, env: !vt
    ) :<f,!ref> void = begin
    if i < n then begin
      f (pf | i, A[i], env); loop (pf | f, A, n, i+1, env)
    end
  end // end of [loop]
  val () = loop (pf | f, A, asz, 0, env)
in
  // empty
end // end of [iforeach_array_main]

implement{a} iforeach_array_clo
  {v} {n} {f} (pf_v | f, A, asz) = let
  stavar l_f: addr
  typedef clo_t = (!v | sizeLt n, a) -<clo,f> void
  val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | i: sizeLt n, x: a, p_f: !ptr l_f):<f> void = let
    prval (pf1, pf2) = pf in !p_f (pf1 | i, x); pf := (pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = iforeach_array_main<a> {V} {ptr l_f} (pf | app, A, asz, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [iforeach_array_clo]

implement{a}
  iforeach_array_cloref {v} {n} {f} (pf | f, A, asz) = let
  viewtypedef cloref_t = (!v | sizeLt n, a) -<cloref,f> void
  fn app (pf: !v | i: sizeLt n, x: a, f: !cloref_t):<f> void = f (pf | i, x)
  val () = iforeach_array_main<a> {v} {cloref_t} (pf | app, A, asz, f)
in
  // empty
end // end of [iforeach_array_cloref]

(* ****** ****** *)

implement{a} array_ptr_alloc (n) =
  array_ptr_alloc_tsz {a} (n, sizeof<a>)

(* ****** ****** *)

// [array.sats] is already loaded by a call to [pervasive_load]
staload _(*anonymous*) = "prelude/SATS/array.sats" // this forces that the static
// loading function for [array.sats] is to be called at run-time
// this is really needed only if some datatypes are declared in [array.sats]

(* ****** ****** *)

%{$

typedef unsigned char byte ;

extern void *memcpy (void *dst, const void* src, size_t n) ;

ats_void_type
atspre_array_ptr_initialize_elt_tsz (
   ats_ptr_type A
 , ats_size_type asz 
 , ats_ptr_type ini
 , ats_size_type tsz
 )  {
  int i, itsz ; int left ; ats_ptr_type p ;
  if (asz == 0) return ;
  memcpy (A, ini, tsz) ;
  i = 1 ; itsz = tsz ; left = asz - i ;
  while (left > 0) {
    p = (ats_ptr_type)(((byte*)A) + itsz) ;
    if (left <= i) {
      memcpy (p, A, left * tsz) ; return ;
    } /* end of [if] */
    memcpy (p, A, itsz);
    i = i + i ; itsz = itsz + itsz ; left = asz - i ;
  } /* end of [while] */
  return ;
} /* end of [atspre_array_ptr_initialize_elt_tsz] */

/* ****** ****** */

ats_void_type
atspre_array_ptr_initialize_fun_tsz_main (
   ats_ptr_type A
 , ats_size_type asz
 , ats_ptr_type f
 , ats_size_type tsz
 , ats_ptr_type env
 ) {
  int i = 0;
  ats_ptr_type p = A ;
  while (i < asz) {
    ((ats_void_type (*)(ats_ptr_type, ats_size_type, ats_ptr_type))f)(p, i, env) ;
    p = (ats_ptr_type)(((byte*)p) + tsz) ;
    ++i ;
  }
  return ;
} /* end of [atspre_array_ptr_initialize_fun_tsz_main] */

ats_void_type
atspre_array_ptr_initialize_clo_tsz_main (
   ats_ptr_type A
 , ats_size_type asz
 , ats_ref_type f
 , ats_size_type tsz
 , ats_ptr_type env
 ) {
  int i = 0;
  ats_ptr_type p = A ;
  while (i < asz) {
    ((ats_void_type (*)(ats_clo_ptr_type, ats_ptr_type, ats_size_type, ats_ptr_type))ats_closure_fun(f))(f, p, i, env) ;
    p = (ats_ptr_type)(((byte*)p) + tsz) ;
    ++i ;
  }
  return ;
} /* atspre_array_ptr_initialize_clo_tsz_main */

/* ****** ****** */

ats_void_type
atspre_foreach_array_ptr_tsz_main (
   ats_ptr_type f
 , ats_ptr_type A
 , ats_size_type asz
 , ats_size_type tsz
 , ats_ptr_type env
 ) {
  int i = 0;
  ats_ptr_type p = A ;
  while (i < asz) {
    ((ats_void_type (*)(ats_ptr_type, ats_ptr_type))f)(p, env) ;
    p = (ats_ptr_type)(((byte*)p) + tsz) ;
    ++i ;
  }
  return ;
} /* atspre_foreach_array_ptr_tsz_main */

ats_void_type
atspre_iforeach_array_ptr_tsz_main (
   ats_ptr_type f
 , ats_ptr_type A
 , ats_size_type asz
 , ats_size_type tsz
 , ats_ptr_type env
 ) {
  int i = 0;
  ats_ptr_type p = A ;
  while (i < asz) {
    ((ats_void_type (*)(ats_size_type, ats_ptr_type, ats_ptr_type))f)(i, p, env) ;
    p = (ats_ptr_type)(((byte*)p) + tsz) ;
    ++i ;
  }
  return ;
} /* atspre_iforeach_array_ptr_tsz_main */

%}

(* ****** ****** *)

(* end of [array.dats] *)
