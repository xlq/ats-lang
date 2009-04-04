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

(* persistent matrices *)

(* ****** ****** *)

absview matrix_v (a:viewt@ype, m:int, n:int, l:addr)

extern prfun array_v_of_matrix_v {a:viewt@ype} {m,n:int} {l:addr}
  (pf_mat: matrix_v (a, m, n, l)):<> [mn:int] (MUL (m, n, mn), array_v (a, mn, l))

extern prfun matrix_v_of_array_v {a:viewt@ype} {m,n:int} {mn:int} {l:addr}
  (pf_mul: MUL (m, n, mn), pf_arr: array_v (a, mn, l)):<> matrix_v (a, m, n, l)

(* ****** ****** *)

local

assume matrix_v
  (a:viewt@ype, m:int, n:int, l:addr) =
  [mn:int] (MUL (m, n, mn), array_v (a, mn, l))
// end of [assume]

in // in of [local]

implement array_v_of_matrix_v (pf_mat) = pf_mat
implement matrix_v_of_array_v (pf_mul, pf_arr) = @(pf_mul, pf_arr)

end // end of [local]

(* ****** ****** *)

assume matrix_viewt0ype_int_int_type
  (a:viewt@ype, m:int, n:int) = [l:addr] @{
  data= ptr l, view= vbox (matrix_v (a, m, n, l))
} // end of [matrix_viewt0ype_int_int_type]

(*
assume matrix_viewt0ype_int_int_type
  (a:viewt@ype, m:int, n:int) = [mn:int] [l:addr] '{
  data= ptr l,
  row= int m,
  col= int n,
  view= vbox (matrix_v (a, m, n, l))
} // end of [matrix_viewt0ype_int_int_type]
*)

(* ****** ****** *)

extern fun vbox_make_view_ptr_matrix {a:viewt@ype} {m,n:int} {l:addr} 
  (pf: matrix_v (a, m, n, l) | p: ptr l):<> (vbox (matrix_v (a, m, n, l)) | void)
  = "atspre_vbox_make_view_ptr"

implement matrix_make_arraysize__main {a} (m, n) =
  lam (pf_mul | arrsz) => let
    prval () = free_gc_elim {a} (arrsz.0) // return the certificate
    prval pf_mat = matrix_v_of_array_v (pf_mul, arrsz.1)
    val (pf_mat_box | ()) = vbox_make_view_ptr_matrix (pf_mat | arrsz.2)
  in @{
    data= arrsz.2, view= pf_mat_box
  } end
// end of [matrix_make_arrsize__main]

(* ****** ****** *)

implement{a} matrix_make_elt (m, n, x) = let
  val (pf_mul | mn) = mul2_size1_size1 (m, n)
  prval () = mul_nat_nat_nat pf_mul
  val (pf_gc, pf_arr | p_arr) =
    array_ptr_alloc_tsz {a} (mn, sizeof<a>)
  // end of [val]
  prval () = free_gc_elim {a} (pf_gc) // return the certificate
  val () = array_ptr_initialize_elt<a> (!p_arr, mn, x)
  prval pf_mat = matrix_v_of_array_v (pf_mul, pf_arr)
  val (pf_mat_box | ()) = vbox_make_view_ptr_matrix (pf_mat | p_arr)
in @{
  data= p_arr, view= pf_mat_box
} end // end of [matrix_make_elt]

(* ****** ****** *)

extern fun natdiv {m,n:pos; mn,i:nat | i < mn}
  (pf: MUL (m, n, mn) | i: size_t i, n: size_t n):<> [d:nat | d < m] size_t d
  = "ats_matrix_natdiv"

%{^

static inline
ats_size_type ats_matrix_natdiv (ats_size_type i, ats_size_type n) {
  return (i / n) ;
}

%}

(* ****** ****** *)

infixl ( * ) szmul2; infixl ( mod ) szmod1

implement matrix_make_fun_tsz__main
  {a} {v} {vt} {m,n} {f:eff} (pf | m, n, f, tsz, env) = let
  val [mn:int] (pf_mul | mn) = m szmul2 n
  prval () = mul_nat_nat_nat pf_mul
  val (pf_gc, pf_arr | p_arr) = array_ptr_alloc_tsz {a} (mn, tsz)
  prval () = free_gc_elim {a} (pf_gc) // return the certificate
  viewtypedef fun_t = (!v | &(a?) >> a, sizeLt m, natLt n, !vt) -<f> void
  var !p_f1 = @lam
    (pf: !v | x: &(a?) >> a, i: sizeLt mn, env: !vt): void =<clo,f> let
    val d = natdiv (pf_mul | i, n) and r = i szmod1 n
  in
    f (pf | x, d, r, env)
  end // end of [f1]
  val () = begin
    array_ptr_initialize_clo_tsz__main {a} {v} {vt} (pf | !p_arr, mn, !p_f1, tsz, env)
  end // end of [val]
  prval pf_mat = matrix_v_of_array_v (pf_mul, pf_arr)
  val (pf_mat_box | ()) = vbox_make_view_ptr_matrix (pf_mat | p_arr)
in @{
  data= p_arr, view= pf_mat_box
} end // end of [matrix_make_fun_tsz__main]

implement matrix_make_clo_tsz
  {a} {m,n} {f:eff} (m, n, f, tsz) = let
  stavar l_f:addr
  val p_f: ptr l_f = &f
  typedef clo_t = (&(a?) >> a, sizeLt m, sizeLt n) -<clo,f> void
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: &(a?) >> a, i: sizeLt m, j: sizeLt n, p_f: !ptr l_f)
    :<f> void = !p_f (x, i, j)
  val M = matrix_make_fun_tsz__main {a} {V} {ptr l_f} (view@ f | m, n, app, tsz, p_f)
in
  M // the returned matrix
end // end of [matrix_make_fun_tsz_cloptr]

(* ****** ****** *)

prfun lemma_for_matrix_subscripting
  {m,n:nat} {i:nat | i < m} {mn,p:int} .<m>.
  (pf1: MUL (m, n, mn), pf2: MUL (i, n, p)): [p+n <= mn] void = let
  prval MULind pf11 = pf1
in
  sif i < m-1 then begin
    lemma_for_matrix_subscripting (pf11, pf2)
  end else let // i = m-1
    prval () = mul_isfun (pf11, pf2)
  in
    // empty
  end // end of [sif]
end // end of [lemma_for_matrix_subscripting]

implement{a} matrix_get_elt_at (M, i, n, j) = let
  prval vbox pf_mat = M.view
  prval (pf_mul_mn, pf_arr) = array_v_of_matrix_v (pf_mat)
  val (pf_mul_i_n | i_n) = i szmul2 n
  prval () = mul_nat_nat_nat pf_mul_i_n
  prval () = lemma_for_matrix_subscripting (pf_mul_mn, pf_mul_i_n)
  val M_data = M.data
  val x = !M_data.[i_n+j]
  prval () = pf_mat := matrix_v_of_array_v (pf_mul_mn, pf_arr)
in
  x // return value
end // end of [matrix_get_elt_at]

implement{a} matrix_set_elt_at (M, i, n, j, x) = let
  prval vbox pf_mat = M.view
  prval (pf_mul_mn, pf_arr) = array_v_of_matrix_v (pf_mat)
  val (pf_mul_i_n | i_n) = i szmul2 n
  prval () = mul_nat_nat_nat pf_mul_i_n
  prval () = lemma_for_matrix_subscripting (pf_mul_mn, pf_mul_i_n)
  val M_data = M.data
  val () = !M_data.[i_n+j] := x
  prval () = pf_mat := matrix_v_of_array_v (pf_mul_mn, pf_arr)
in
  // empty
end // end of [matrix_set_elt_at]

(* ****** ****** *)

implement{a} matrix_get_elt_at__intsz (M, i, n, j) = let
  val i = i2sz i; val n = i2sz n; val j = i2sz j
in
  matrix_get_elt_at<a> (M, i, n, j)
end // end of [matrix_get_elt_at__intsz]

implement{a} matrix_set_elt_at__intsz (M, i, n, j, x) = let
  val i = i2sz i; val n = i2sz n; val j = i2sz j
in
  matrix_set_elt_at<a> (M, i, n, j, x)
end // end of [matrix_set_elt_at__intsz]

(* ****** ****** *)

fn matrix_ptr_takeout_tsz {a:viewt@ype}
  {m,n:int} {i,j:nat | i < m; j < n} {l0:addr} (
    pf_mat: matrix_v (a, m, n, l0)
  | base: ptr l0, i: size_t i, n: size_t n, j: size_t j, tsz: sizeof_t a
  ) :<> [l:addr] (
      a @ l
    , a @ l -<lin,prf> matrix_v (a, m, n, l0)
    | ptr l
    ) = let
  prval (pf_mul_mn, pf_arr) = array_v_of_matrix_v {a} (pf_mat)
  val (pf_mul_i_n | i_n) = i szmul2 n
  prval () = mul_nat_nat_nat pf_mul_i_n
  prval () = lemma_for_matrix_subscripting (pf_mul_mn, pf_mul_i_n)
  val [l:addr] (pf1, fpf2 | p_ofs) =
    array_ptr_takeout_tsz {a} (pf_arr | base, i_n + j, tsz)
  prval fpf2 =
    llam (pf1: a @ l) =<prf> matrix_v_of_array_v (pf_mul_mn, fpf2 pf1)
in
  (pf1, fpf2 | p_ofs)
end // end of [val]

(* ****** ****** *)

implement{a} matrix_foreach__main
  {v} {vt} {m,n} (pf | f, M, m, n, env) = let
  typedef fun_t = (!v | &a, !vt) -<fun> void
  typedef mat_t = matrix (a, m, n)
  fn* loop1 {i:nat | i <= m} .<m-i+1,0>. (
      pf: !v
    | f: fun_t
    , M: mat_t, m: size_t m, n: size_t n, i: size_t i
    , env: !vt
    ) :<!ref> void = begin
    if i < m then loop2 (pf | f, M, m, n, i, 0, env) else ()
  end // end of [loop1]

  and loop2 {i,j:nat | i < m; j <= n} .<m-i,n-j+1>. (
      pf: !v
    | f: fun_t
    , M: mat_t, m: size_t m, n: size_t n, i: size_t i, j: size_t j
    , env: !vt
    ) :<!ref> void = begin
    if j < n then let
      val () = () where {
        prval vbox pf_mat = M.view
        val (pf1, fpf2 | p_ij) =
          matrix_ptr_takeout_tsz (pf_mat | M.data, i, n, j, sizeof<a>)
        val () = f (pf | !p_ij, env)
        val () = pf_mat := fpf2 (pf1)
      } // end of [val]
    in
      loop2 (pf | f, M, m, n, i, j+1, env)
    end else begin
      loop1 (pf | f, M, m, n, i+1, env)
    end
  end // end of [loop2]
in
  loop1 (pf | f, M, m, n, 0, env)
end // end of [matrix_foreach__main]

implement{a} matrix_foreach_clo {v} {m,n} (pf_v | f, M, m, n) = let
  stavar l_f: addr
  val p_f: ptr l_f = &f
  typedef clo_t = (!v | &a) -<clo> void
  viewdef V = @(v, clo_t @ l_f)
  fn app (pf: !V | x: &a, p_f: !ptr l_f):<> void = let
    prval (pf1, pf2) = pf in !p_f (pf1 | x); pf := @(pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = matrix_foreach__main<a> {V} {ptr l_f} (pf | app, M, m, n, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [matrix_foreach_clo]

implement{a} matrix_foreach_cloref
  {v} {m,n} (pf | f, M, m, n) = let
  viewtypedef cloref_t = (!v | &a) -<cloref> void
  fn app (pf: !v | x: &a, f: !cloref_t):<> void = f (pf | x)
  val () = matrix_foreach__main<a> {v} {cloref_t} (pf | app, M, m, n, f)
in
  // empty
end // end of [matrix_foreach_cloref]

(* ****** ****** *)

implement{a} matrix_iforeach__main
  {v} {vt} {m,n} (pf | f, M, m, n, env) = let
  typedef fun_t = (!v | sizeLt m, sizeLt n, &a, !vt) -<fun> void
  typedef mat_t = matrix (a, m, n)
  fn* loop1 {i:nat | i <= m} .<m-i+1,0>.
    (pf: !v | f: fun_t, M: mat_t, m: size_t m, n: size_t n, i: size_t i, env: !vt)
    :<!ref> void = begin
    if i < m then loop2 (pf | f, M, m, n, i, 0, env) else ()
  end // end of [loop1]

  and loop2 {i,j:nat | i < m; j <= n} .<m-i,n-j+1>. (
      pf: !v
    | f: fun_t, M: mat_t, m: size_t m, n: size_t n, i: size_t i, j: size_t j, env: !vt
    ) :<!ref> void = begin
    if j < n then let
      val () = () where {
        prval vbox pf_mat = M.view
        val (pf1, fpf2 | p_ij) =
          matrix_ptr_takeout_tsz (pf_mat | M.data, i, n, j, sizeof<a>)
        val () = f (pf | i, j, !p_ij, env)
        val () = pf_mat := fpf2 (pf1)
      } // end of [val]
    in
      loop2 (pf | f, M, m, n, i, j+1, env)
    end else begin
      loop1 (pf | f, M, m, n, i+1, env)
    end
  end // end of [loop2]
in
  loop1 (pf | f, M, m, n, 0, env)
end // end of [matrix_iforeach__main]

implement{a} matrix_iforeach_clo
  {v} {m,n} (pf_v | f, M, m, n) = let
  stavar l_f: addr
  val p_f: ptr l_f = &f
  typedef clo_t = (!v | sizeLt m, sizeLt n, &a) -<clo> void
  viewdef V = @(v, clo_t @ l_f)
  fn app
    (pf: !V | i: sizeLt m, j: sizeLt n, x: &a, p_f: !ptr l_f):<> void = let
    prval (pf1, pf2) = pf
  in
    !p_f (pf1 | i, j, x); pf := (pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = matrix_iforeach__main<a> {V} {ptr l_f} (pf | app, M, m, n, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [matrix_iforeach_cloptr]

implement{a}
  matrix_iforeach_cloref {v} {m,n} (pf | f, M, m, n) = let
  viewtypedef cloref_t = (!v | sizeLt m, sizeLt n, &a) -<cloref> void
  fn app (pf: !v | i: sizeLt m, j: sizeLt n, x: &a, f: !cloref_t):<> void =
    f (pf | i, j, x)
  val () = matrix_iforeach__main<a> {v} {cloref_t} (pf | app, M, m, n, f)
in
  // empty
end // end of [matrix_iforeach_cloref]

(* ****** ****** *)

// [matrix.sats] is already loaded by a call to [pervasive_load]
staload _(*anonymous*) = "prelude/SATS/matrix.sats" // this forces that the static
// loading function for [matrix.sats] is to be called at run-time
// this is really needed only if some datatypes are declared in [matrix.sats]

(* ****** ****** *)

(* end of [matrix.dats] *)
