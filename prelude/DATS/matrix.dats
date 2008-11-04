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

(* persistent matrices *)

(* ****** ****** *)

assume matrix_viewt0ype_int_int_type
  (a:viewt@ype, m:int, n:int) = [mn:int] [l:addr] @{
  data= ptr l, mul= MUL (m, n, mn), view= vbox (array_v (a, mn, l))
} // end of [matrix_viewt0ype_int_int_type]

(*
assume matrix_viewt0ype_int_int_type
  (a:viewt@ype, m:int, n:int) = [mn:int] [l:addr] '{
  data= ptr l,
  row= int m,
  col= int n,
  mul= MUL (m, n, mn),
  view= vbox (array_v (a, mn, l))
} // end of [matrix_viewt0ype_int_int_type]
*)

(* ****** ****** *)

implement matrix_main {a} (m, n) = lam (pf_mul | asz) => let
  val (pf_box | ()) = vbox_make_view_ptr_gc (asz.0, asz.1 | asz.2)
in @{
  data= asz.2, mul= pf_mul, view= pf_box
} end // end of [matrix_main]

(* ****** ****** *)

implement{a} matrix_make_elt (m, n, x) = let
  val (pf_mul | mn) = m imul2 n
  prval () = mul_nat_nat_nat pf_mul
  val (pf_gc, pf_arr | ptr) = array_ptr_make_elt<a> (mn, x)
  val (pf_box | ()) = vbox_make_view_ptr_gc (pf_gc, pf_arr | ptr)
in @{
  data= ptr, mul= pf_mul, view= pf_box
} end // end of [matrix_make_elt]

(* ****** ****** *)

extern fun natdiv {m,n:pos; mn,i:nat | i < mn}
  (pf: MUL (m, n, mn) | i: int i, n: int n):<> [d:nat | d < m] int d
  = "ats_matrix_natdiv"

%{^

static inline
ats_int_type ats_matrix_natdiv (ats_int_type i, ats_int_type n) {
  return (i / n) ;
}

%}

(* ****** ****** *)

implement matrix_make_fun_tsz_main
  {a} {v} {vt} {m,n} {f:eff} (pf | m, n, f, tsz, env) = let
  val [mn:int] (pf_mul | mn) = m imul2 n
  prval () = mul_nat_nat_nat pf_mul
  val (pf_gc, pf_arr | p_arr) = array_ptr_alloc_tsz {a} (mn, tsz)
  viewtypedef fun_t = (!v | &(a?) >> a, natLt m, natLt n, !vt) -<f> void
  fn f1 (pf: !v | x: &(a?) >> a, i: natLt mn, env: !vt):<cloptr,f> void = let
    val d = natdiv (pf_mul | i, n) and r = i nmod1 n
  in
    f (pf | x, d, r, env)
  end
  val () = begin
    array_ptr_initialize_fun_tsz_mainclo {a} {v} {vt} (pf | !p_arr, mn, f1, tsz, env)
  end
  val () = cloptr_free (f1)
  val (pf_box | ()) = vbox_make_view_ptr_gc (pf_gc, pf_arr | p_arr)
in @{
  data= p_arr, mul= pf_mul, view= pf_box
} end // end of [matrix_make_fun_tsz_main]

implement matrix_make_fun_tsz_cloptr
  {a} {m,n} {f:eff} (m, n, f, tsz) = let
  viewtypedef cloptr_t = (&(a?) >> a, natLt m, natLt n) -<cloptr,f> void
  fn app (pf: !unit_v | x: &(a?) >> a, i: natLt m, j: natLt n, f: !cloptr_t)
    :<f> void = f (x, i, j)
  prval pf = unit_v ()
  val M = matrix_make_fun_tsz_main {a} {unit_v} {cloptr_t} (pf | m, n, app, tsz, f)
  prval unit_v () = pf
in
  M // the returned matrix
end // end of [matrix_make_fun_tsz_cloptr]

(* ****** ****** *)

prfn lemma_for_matrix_get_and_set
  {m,n,i:nat; mn,p:int | i < m}
  (pf1: MUL (m, n, mn), pf2: MUL (i, n, p)): [p+n <= mn] void = let
  prval pf1 = mul_commute pf1
  prval pf2 = mul_negate (MULind pf2)
  prval pf2 = mul_commute pf2
  prval pf3 = mul_distribute (pf1, pf2)
  prval () = mul_nat_nat_nat pf3
in
  // empty
end // end of [lemma_for_matrix_get_and_set]

implement{a} matrix_get_elt_at (M, n, i, j) = let
  prval pf_mul_mn = M.mul
  val (pf_mul_i_n | i_n) = i imul2 n
  prval () = mul_nat_nat_nat pf_mul_i_n
  prval () = lemma_for_matrix_get_and_set (pf_mul_mn, pf_mul_i_n)
  val M_data = M.data
  prval vbox pf_arr = M.view
in
  !M_data.[i_n+j]
end // end of [matrix_get_elt_at]

implement{a} matrix_set_elt_at (M, n, i, j, x) = let
  prval pf_mul_mn = M.mul
  val (pf_mul_i_n | i_n) = i imul2 n
  prval () = mul_nat_nat_nat pf_mul_i_n
  prval () = lemma_for_matrix_get_and_set (pf_mul_mn, pf_mul_i_n)
  val M_data = M.data
  prval vbox pf_arr = M.view
in
  !M_data.[i_n+j] := x
end // end of [matrix_set_elt_at]

(* ****** ****** *)

implement{a} foreach_matrix_main
  {v} {vt} {m,n} {f:eff} (pf | f, M, m, n, env) = let
  typedef fun_t = (!v | a, !vt) -<fun,f> void
  typedef mat_t = matrix (a, m, n)
  fn* loop1 {i:nat | i <= m} .<m-i+1,0>.
    (pf: !v | f: fun_t, M: mat_t, m: int m, n: int n, i: int i, env: !vt)
    :<f,!ref> void = begin
    if i < m then loop2 (pf | f, M, m, n, i, 0, env) else ()
  end // end of [loop1]

  and loop2 {i,j:nat | i < m; j <= n} .<m-i,n-j+1>.
    (pf: !v | f: fun_t, M: mat_t, m: int m, n: int n, i: int i, j: int j, env: !vt)
    :<f,!ref> void = begin
    if j < n then let
      val () = f (pf | matrix_get_elt_at (M, n, i, j), env)
    in
      loop2 (pf | f, M, m, n, i, j+1, env)
    end else begin
      loop1 (pf | f, M, m, n, i+1, env)
    end
  end // end of [loop2]
in
  loop1 (pf | f, M, m, n, 0, env)
end // end of [foreach_matrix_main]

implement{a} foreach_matrix_cloptr {m,n} {f:eff} (f, M, m, n) = let
  viewtypedef cloptr_t = a -<cloptr,f> void
  fn app (pf: !unit_v | x: a, f: !cloptr_t):<f> void = f (x)
  prval pf = unit_v ()
  val () = foreach_matrix_main<a> {unit_v} {cloptr_t} (pf | app, M, m, n, f)
  prval unit_v () = pf
in
  // empty
end // end of [foreach_matrix_cloptr]

implement{a} foreach_matrix_cloref {m,n} {f:eff} (f, M, m, n) = let
  viewtypedef cloref_t = a -<cloref,f> void
  fn app (pf: !unit_v | x: a, f: !cloref_t):<f> void = f (x)
  prval pf = unit_v ()
  val () = foreach_matrix_main<a> {unit_v} {cloref_t} (pf | app, M, m, n, f)
  prval unit_v () = pf
in
  // empty
end // end of [foreach_matrix_cloref]

(* ****** ****** *)

implement{a} iforeach_matrix_main
  {v} {vt} {m,n} {f:eff} (pf | f, M, m, n, env) = let
  typedef fun_t = (!v | natLt m, natLt n, a, !vt) -<fun,f> void
  typedef mat_t = matrix (a, m, n)
  fn* loop1 {i:nat | i <= m} .<m-i+1,0>.
    (pf: !v | f: fun_t, M: mat_t, m: int m, n: int n, i: int i, env: !vt)
    :<f,!ref> void = begin
    if i < m then loop2 (pf | f, M, m, n, i, 0, env) else ()
  end // end of [loop1]

  and loop2 {i,j:nat | i < m; j <= n} .<m-i,n-j+1>.
    (pf: !v | f: fun_t, M: mat_t, m: int m, n: int n, i: int i, j: int j, env: !vt)
    :<f,!ref> void = begin
    if j < n then let
      val () = f (pf | i, j, matrix_get_elt_at (M, n, i, j), env)
    in
      loop2 (pf | f, M, m, n, i, j+1, env)
    end else begin
      loop1 (pf | f, M, m, n, i+1, env)
    end
  end // end of [loop2]
in
  loop1 (pf | f, M, m, n, 0, env)
end // end of [iforeach_matrix_main]

implement{a} iforeach_matrix_cloptr {m,n} {f:eff} (f, M, m, n) = let
  viewtypedef cloptr_t = (natLt m, natLt n, a) -<cloptr,f> void
  fn app (pf: !unit_v | i: natLt m, j: natLt n, x: a, f: !cloptr_t):<f> void =
    f (i, j, x)
  prval pf = unit_v ()
  val () = iforeach_matrix_main<a> {unit_v} {cloptr_t} (pf | app, M, m, n, f)
  prval unit_v () = pf
in
  // empty
end // end of [iforeach_matrix_cloptr]

implement{a} iforeach_matrix_cloref {m,n} {f:eff} (f, M, m, n) = let
  viewtypedef cloref_t = (natLt m, natLt n, a) -<cloref,f> void
  fn app (pf: !unit_v | i: natLt m, j: natLt n, x: a, f: !cloref_t):<f> void =
    f (i, j, x)
  prval pf = unit_v ()
  val () = iforeach_matrix_main<a> {unit_v} {cloref_t} (pf | app, M, m, n, f)
  prval unit_v () = pf
in
  // empty
end // end of [iforeach_matrix_cloref]

(* ****** ****** *)

(* end of [matrix.dats] *)
