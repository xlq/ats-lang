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
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(*
**
** Various kinds of (generic) arrays
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Shivkumar Chandrasekaran (shiv AT ece DOT ucsb DOT edu)
**
** Time: Summer, 2009
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

staload "libats/SATS/fmatrix.sats"
staload "libats/SATS/genarrays.sats"

(* ****** ****** *)

infixl (imul) szmul
#define szmul mul_size_size
#define sz2sz size1_of_size

(* ****** ****** *)

implement{a} GEVEC_ptr_takeout
  {n} {d} {l0} (pf_vec | p_vec, d, i) = let
  viewdef V0 = GEVEC_v (a, n, d, l0)
  val ofs = (i * d) szmul sizeof<a>
  val [ofs:int] ofs = sz2sz (ofs) // no-op casting
  stadef l = l0 + ofs
  prval (pf_at, fpf_vec) = __cast (pf_vec) where {
    extern prfun __cast (pf: V0): (a @ l, a @ l -<lin,prf> V0)
  } // end of [prval]
in
  #[l | (pf_at, fpf_vec | p_vec + ofs) ]
end // end of [GEVEC_ptr_takeout]

(* ****** ****** *)

implement{a1} GEVEC_ptr_split
  {n,i} {d} {l0} (pf_vec | p_vec, d, i) = let
  viewdef V0 (a: viewt@ype) = GEVEC_v (a, n, d, l0)
  val ofs = (i * d) szmul sizeof<a1>
  val [ofs:int] ofs = sz2sz (ofs) // no-op casting
  stadef l = l0 + ofs
  viewdef V1 (a: viewt@ype) = GEVEC_v (a, i, d, l0)
  viewdef V2 (a: viewt@ype) = GEVEC_v (a, n-i, d, l)
  prval (pf1_vec, pf2_vec, fpf_vec) = __cast (pf_vec) where {
    extern prfun __cast (pf: V0 a1):
      (V1 a1, V2 a1, {a2:viewt@ype | a1 \tszeq a2} (V1 a2, V2 a2) -<prf> V0 a2)
  } // end of [prval]
in
  #[l | (pf1_vec, pf2_vec, fpf_vec | p_vec + ofs) ]
end // end of [GEVEC_ptr_split]

(* ****** ****** *)

implement{a} GEVEC_ptr_get_elt_at (V, d, i) = x where {
  val (pf, fpf | p) = GEVEC_ptr_takeout<a> (view@ V | &V, d, i)
  val x = !p
  prval () = view@ V := fpf (pf)
} // end of [GEVEC_ptr_get_elt_at]

implement{a} GEVEC_ptr_set_elt_at (V, d, i, x) = () where {
  val (pf, fpf | p) = GEVEC_ptr_takeout<a> (view@ V | &V, d, i)
  val () = !p := x
  prval () = view@ V := fpf (pf)
} // end of [GEVEC_ptr_set_elt_at]

(* ****** ****** *)

// X <- alpha
implement{a}
  GEVEC_ptr_initialize_elt
    {m} {incX} (X, m, incX, alpha) = let
  val (pf_mul | ofs) = mul2_size1_size1 (incX, sizeof<a>)
  fun loop {n:nat} {lX:addr} .<n>. (
      pf_vec: !GEVEC_v (a?, n, incX, lX) >> GEVEC_v (a, n, incX, lX)
    | pX: ptr lX, n: size_t n
    ) :<cloref> void =
    if n > 0 then let
      prval (pf_at, pf1_vec) = GEVEC_v_uncons {a?} (pf_mul, pf_vec)
      val () = !pX := alpha
      val () = loop (pf1_vec | pX + ofs, n-1)
      prval () = pf_vec := GEVEC_v_cons {a} (pf_mul, pf_at, pf1_vec)
    in
      // nothing
    end else let
      prval () = GEVEC_v_unnil (pf_vec)
      prval () = pf_vec := GEVEC_v_nil {a} {incX} {lX} ()
    in
      // nothing
    end // end of [if]
  // end of [loop]
in
   loop (view@ X | &X, m)
end // end of [GEVEC_ptr_initialize_elt]

(* ****** ****** *)

implement{a} GEVEC_ptr_copy
  {m} {d1,d2} (X1, X2, m, d1, d2) = let
  val (pf1_mul | ofs1) = mul2_size1_size1 (d1, sizeof<a>)
  val (pf2_mul | ofs2) = mul2_size1_size1 (d2, sizeof<a>)
  fun loop {mi:nat | mi <= m} {l1,l2:addr} .<mi>. (
      pf1: !GEVEC_v (a, mi, d1, l1)
    , pf2: !GEVEC_v (a?, mi, d2, l2) >> GEVEC_v (a, mi, d2, l2)
    | p1: ptr l1, p2: ptr l2, mi: size_t mi
    ) :<cloref> void =
    if mi > 0 then let
      prval (pf11, pf12) = GEVEC_v_uncons {a} (pf1_mul, pf1)
      prval (pf21, pf22) = GEVEC_v_uncons {a?} (pf2_mul, pf2)
      val () = !p2 := !p1
      val () = loop (pf12, pf22 | p1+ofs1, p2+ofs2, mi-1)
      prval () = pf1 := GEVEC_v_cons {a} (pf1_mul, pf11, pf12)
      prval () = pf2 := GEVEC_v_cons {a} (pf2_mul, pf21, pf22)
    in
      // empty
    end else let
      prval () = GEVEC_v_unnil (pf2) in pf2 := GEVEC_v_nil {a} ()
    end // end of [if]
in
  loop (view@ X1, view@ X2 | &X1, &X2, m)
end // end of [GEVEC_ptr_copy]

(* ****** ****** *)

implement
  GEVEC_ptr_foreach_fun_tsz__main
    {a} {v} {vt} {n} {d}
    (pf | base, f, vsz, inc, tsz, env) = let
  val (pf_mul | ofs) = mul2_size1_size1 (inc, tsz)
  fun loop {l:addr} {n:nat} .<n>. (
      pf: !v
    , pf_vec: !GEVEC_v (a, n, d, l)
    | p: ptr l, n: size_t n, env: !vt
    ) :<cloref> void =
    if n > 0 then let
      prval (pf_at, pf1_vec) = GEVEC_v_uncons {a} (pf_mul, pf_vec)
      val () = f (pf | !p, env)
      val () = loop (pf, pf1_vec | p+ofs, n-1, env)
      prval () = pf_vec := GEVEC_v_cons {a} (pf_mul, pf_at, pf1_vec)
    in
      // nothing
    end // end of [if]
  (* end of [loop] *)
in
  loop (pf, view@ base | &base, vsz, env)
end // end of [GEVEC_ptr_foreach_fun_tsz__main]

//

implement{a} GEVEC_ptr_foreach_fun
  {v} (pf | base, f, n, inc) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (!v | &a) -<> void) :<> (!v | &a, !ptr) -<> void
  } // end of [where]
in
  GEVEC_ptr_foreach_fun_tsz__main (pf | base, f, n, inc, sizeof<a>, null)
end // end of [GEVEC_ptr_foreach_fun_tsz]

//

implement{a} GEVEC_ptr_foreach_clo
  {v} (pf_v | base, f, vsz, inc) = let
  stavar l_f: addr
  val p_f: ptr l_f = &f
  typedef clo_t = (!v | &a) -<clo> void
  viewdef V = @(v, clo_t @ l_f)
  fn app (pf: !V | x: &a, p_f: !ptr l_f):<> void = let
    prval (pf1, pf2) = pf in !p_f (pf1 | x); pf := @(pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = GEVEC_ptr_foreach_fun_tsz__main
    {a} {V} {ptr l_f} (pf | base, app, vsz, inc, sizeof<a>, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [GEVEC_ptr_foreach_clo]

(* ****** ****** *)

implement
  GEVEC_ptr_iforeach_fun_tsz__main
    {a} {v} {vt} {n} {d}
    (pf | base, f, vsz, inc, tsz, env) = let
  val (pf_mul | ofs) = mul2_size1_size1 (inc, tsz)
  fun loop {l:addr}
    {ni:nat | ni <= n} .<ni>. (
      pf: !v
    , pf_vec: !GEVEC_v (a, ni, d, l)
    | p: ptr l, ni: size_t ni, env: !vt
    ) :<cloref> void =
    if ni > 0 then let
      prval (pf_at, pf1_vec) = GEVEC_v_uncons {a} (pf_mul, pf_vec)
      val () = f (pf | vsz - ni, !p, env)
      val () = loop (pf, pf1_vec | p+ofs, ni-1, env)
      prval () = pf_vec := GEVEC_v_cons {a} (pf_mul, pf_at, pf1_vec)
    in
      // nothing
    end // end of [if]
  (* end of [loop] *)
in
  loop (pf, view@ base | &base, vsz, env)
end // end of [GEVEC_ptr_iforeach_fun_tsz__main]

//

implement{a} GEVEC_ptr_iforeach_fun
  {v} {n} (pf | base, f, n, inc) = let
  val f = coerce (f) where {
    extern castfn coerce
      (f: (!v | sizeLt n, &a) -<> void)
      :<> (!v | sizeLt n, &a, !ptr) -<> void
  } // end of [where]
in
  GEVEC_ptr_iforeach_fun_tsz__main (pf | base, f, n, inc, sizeof<a>, null)
end // end of [GEVEC_ptr_iforeach_fun_tsz]

(* ****** ****** *)

implement
  GEVEC_ptr_iforeach_clo_tsz__main
    {a} {v} {vt} {n} {d}
    (pf | base, f, vsz, inc, tsz, env) = let
  val (pf_mul | ofs) = mul2_size1_size1 (inc, tsz)
  fun loop {l:addr}
    {ni:nat | ni <= n} .<ni>. (
      pf: !v
    , pf_vec: !GEVEC_v (a, ni, d, l)
    | p: ptr l
    , f: &(!v | sizeLt n, &a, !vt) -<clo> void
    , ni: size_t ni, env: !vt
    ) :<cloref> void =
    if ni > 0 then let
      prval (pf_at, pf1_vec) = GEVEC_v_uncons {a} (pf_mul, pf_vec)
      val () = f (pf | vsz - ni, !p, env)
      val () = loop (pf, pf1_vec | p+ofs, f, ni-1, env)
      prval () = pf_vec := GEVEC_v_cons {a} (pf_mul, pf_at, pf1_vec)
    in
      // nothing
    end // end of [if]
  (* end of [loop] *)
in
  loop (pf, view@ base | &base, f, vsz, env)
end // end of [GEVEC_ptr_iforeach_clo_tsz__main]

//

implement{a} GEVEC_ptr_iforeach_clo
  {v} {n} (pf | base, f, n, inc) = let
  stavar l_f: addr
  val p_f = (&f: ptr l_f)
  typedef clo_t = (!v | sizeLt n, &a) -<clo> void
  typedef clo1_t = (!v | sizeLt n, &a, !ptr) -<clo> void
  prval () = view@ f := coerce (view@ f) where {
    extern prfun coerce (pf_clo: clo_t @ l_f): clo1_t @ l_f
  } // end of [where]
  val () = GEVEC_ptr_iforeach_clo_tsz__main {a} {v} {ptr} (pf | base, f, n, inc, sizeof<a>, null)
  prval () = view@ f := coerce (view@ f) where {
    extern prfun coerce (pf_clo: clo1_t @ l_f): clo_t @ l_f
  }
in
  // nothing
end // end of [GEVEC_ptr_iforeach_clo_tsz]

(* ****** ****** *)

implement MATVECINC_get (pf | x1, x2, ld) =
  case+ (x1, x2) of
  | (ORDERrow (), ORDERrow ()) => let
      prval MATVECINCrowrow () = pf in 1 end
    // end [row, row]
  | (ORDERrow (), ORDERcol ()) => let
      prval MATVECINCrowcol () = pf in ld end
    // end [row, col]
  | (ORDERcol (), ORDERrow ()) => let
      prval MATVECINCcolrow () = pf in ld end
    // end [col, row]
  | (ORDERcol (), ORDERcol ()) => let
      prval MATVECINCcolcol () = pf in 1 end
    // end [col, col]
// end of [MATVECINC_get]

(* ****** ****** *)

implement{a} GEMAT_ptr_takeout
  {ord} {m, n} {lda} {l0}
  (pf_mat | ord, p_mat, lda, i, j) = let
  viewdef V0 = GEMAT_v (a, m, n, ord, lda, l0)
  val ofs = (case+ ord of
    | ORDERrow () => (i szmul lda + j) * sizeof<a>
    | ORDERcol () => (i + j szmul lda) * sizeof<a>
  ) : size_t
  val [ofs:int] ofs = sz2sz (ofs)
  stadef l = l0 + ofs
  prval (pf_at, fpf_mat) = __cast (pf_mat) where {
    extern prfun __cast (pf: V0): (a @ l, a @ l -<lin,prf> V0)
  } // end of [prval]
in
  #[l | (pf_at, fpf_mat | p_mat + ofs) ]
end // end of [GEMAT_ptr_takeout]

(* ****** ****** *)

implement{a} GEMAT_ptr_get_elt_at (ord, A, lda, i, j) = let
  val (pf, fpf | p) = GEMAT_ptr_takeout<a> (view@ A | ord, &A, lda, i, j)
  val x = !p
  prval () = view@ A := fpf (pf)
in
  x // the return value
end // end of [GEMAT_ptr_get_elt_at]

implement{a} GEMAT_ptr_set_elt_at (ord, A, lda, i, j, x) = let
  val (pf, fpf | p) = GEMAT_ptr_takeout<a> (view@ A | ord, &A, lda, i, j)
  val () = !p := x
  prval () = view@ A := fpf (pf)
in
  // nothing
end // end of [GEMAT_ptr_set_elt_at]

(* ****** ****** *)

implement{a} GEMAT_ptr_tail_row
  {ord} {m,n} {lda} {l0}
  (pf_mat | ord, p_mat, lda) = let
  viewdef V0 = GEMAT_v (a, m, n, ord, lda, l0)
  val ofs = (case+ ord of
    | ORDERrow () => lda * sizeof<a> | ORDERcol () => sizeof<a>
  ) : size_t // end of [val]
  val [ofs:int] ofs = sz2sz (ofs)
  stadef l = l0 + ofs
  viewdef V1 = GEMAT_v (a, m-1, n, ord, lda, l)
  prval (pf1_mat, fpf_mat) = __cast (pf_mat) where {
    extern prfun __cast (pf: V0): (V1, V1 -<lin,prf> V0)
  } // end of [prval]
in
  #[l | (pf1_mat, fpf_mat | p_mat + ofs) ]
end // end of [GEMAT_ptr_tail_row]

(* ****** ****** *)

implement{a} GEMAT_ptr_tail_col
  {ord} {m,n} {lda} {l0}
  (pf_mat | ord, p_mat, lda) = let
  viewdef V0 = GEMAT_v (a, m, n, ord, lda, l0)
  val ofs = (case+ ord of
    | ORDERrow () => sizeof<a> | ORDERcol () => lda * sizeof<a>
  ) : size_t // end of [val]
  val [ofs:int] ofs = sz2sz (ofs)
  stadef l = l0 + ofs
  viewdef V1 = GEMAT_v (a, m, n-1, ord, lda, l)
  prval (pf1_mat, fpf_mat) = __cast (pf_mat) where {
    extern prfun __cast (pf: V0): (V1, V1 -<lin,prf> V0)
  } // end of [prval]
in
  #[l | (pf1_mat, fpf_mat | p_mat + ofs) ]
end // end of [GEMAT_ptr_tail_col]

(* ****** ****** *)

extern fun GEMAT_ptr_split1x2_tsz {a1:viewt@ype}
  {ord:order} {m,n,j:nat | j <= n} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a1, m, n, ord, lda, l0)
  | ord: ORDER ord, p_mat: ptr l0, lda: size_t lda, j: size_t j, tsz: sizeof_t a1
  ) :<> GEMAT_ptr_split1x2_res_t (a1, m, n, j, ord, lda, l0)

implement GEMAT_ptr_split1x2_tsz
  {a1} {ord} {m,n,j} {lda} {l0}
  (pf_mat | ord, p_mat, lda, j, tsz) = let
  val ofs = (case ord of
    | ORDERrow () => j szmul tsz | ORDERcol () => (j * lda) szmul tsz
  ) : size_t // end of [val]
  val ofs = sz2sz (ofs)
  val res = (unit_v, unit_v, unit_p | p_mat, p_mat + ofs)
  extern castfn __cast {vt:viewt@ype}
    (pf: GEMAT_v (a1, m, n, ord, lda, l0) | res: vt)
    :<> GEMAT_ptr_split1x2_res_t (a1, m, n, j, ord, lda, l0)
  // end of [__cast]
in
  __cast (pf_mat | res)
end // end of [GEMAT_ptr_split1x2_tsz]

implement{a1} GEMAT_ptr_split1x2
  (pf_mat | ord, p_mat, lda, j) =
  GEMAT_ptr_split1x2_tsz {a1} (pf_mat | ord, p_mat, lda, j, sizeof<a1>)
// end of [GEMAT_ptr_split1x2]

(* ****** ****** *)

extern
fun GEMAT_ptr_split2x1_tsz {a1:viewt@ype}
  {ord:order} {m,n,i:nat | i <= m} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a1, m, n, ord, lda, l0)
  | ord: ORDER ord, p_mat: ptr l0, lda: size_t lda, i: size_t i, tsz: sizeof_t a1
  ) :<> GEMAT_ptr_split2x1_res_t (a1, m, n, i, ord, lda, l0)

implement GEMAT_ptr_split2x1_tsz
  {a1} {ord} {m,n,i} {lda} {l0}
  (pf_mat | ord,p_mat, lda, i, tsz) = let
  val ofs = (case ord of
    | ORDERrow () => (i * lda) szmul tsz | ORDERcol () => i szmul tsz
  ) : size_t // end of [val]
  val ofs = sz2sz (ofs)
  val res = (unit_v, unit_v, unit_p | p_mat, p_mat + ofs)
  extern castfn __cast {vt:viewt@ype}
    (pf: GEMAT_v (a1, m, n, ord, lda, l0) | res: vt)
    :<> GEMAT_ptr_split2x1_res_t (a1, m, n, i, ord, lda, l0)
  // end of [__cast]
in
  __cast (pf_mat | res)
end // end of [GEMAT_ptr_split2x1_tsz]

implement{a1} GEMAT_ptr_split2x1
  (pf_mat | ord, p_mat, lda, i) =
  GEMAT_ptr_split2x1_tsz {a1} (pf_mat | ord, p_mat, lda, i, sizeof<a1>)
// end of [GEMAT_ptr_split2x1]

(* ****** ****** *)

extern
fun GEMAT_ptr_split2x2_tsz {a1:viewt@ype}
  {ord:order} {m,n,i,j:nat | i <= m; j <= n} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a1, m, n, ord, lda, l0)
  | ord: ORDER ord, p_mat: ptr l0, lda: size_t lda, i: size_t i, j: size_t j, tsz: sizeof_t a1
  ) :<> GEMAT_ptr_split2x2_res_t (a1, m, n, i, j, ord, lda, l0)

implement GEMAT_ptr_split2x2_tsz
  {a1} {ord} {m,n,i,j} {lda} {l0}
  (pf_mat | ord, p_mat, lda, i, j, tsz) = let
  val res = (case+ ord of
    | ORDERrow () => let
        val i_tmp = sz2sz (j * tsz) // no-op casting
        val p_tmp = p_mat + sz2sz ((i * lda) szmul tsz)
      in @(
        unit_v, unit_v, unit_v, unit_v, unit_p
      | p_mat, p_mat + i_tmp, p_tmp, p_tmp + i_tmp
      ) end // end of [ORDERrow]
    | ORDERcol () => let
        val i_tmp = sz2sz (i * tsz) // no-op casting
        val p_tmp = p_mat + sz2sz ((j * lda) szmul tsz)
      in @(
        unit_v, unit_v, unit_v, unit_v, unit_p
      | p_mat, p_tmp, p_mat + i_tmp, p_tmp + i_tmp
      ) end // end of [ORDERcol]
  ) : (
    unit_v, unit_v, unit_v, unit_v, unit_p | ptr, ptr, ptr, ptr
  ) // end of [val]
   extern castfn __cast {vt:viewt@ype}
     (pf: GEMAT_v (a1, m, n, ord, lda, l0) | res: vt)
     :<> GEMAT_ptr_split2x2_res_t (a1, m, n, i, j, ord, lda, l0)
  // end of [__cast]
in
  __cast (pf_mat | res)
end // end of [GEMAT_ptr_split2x2_tsz]

implement{a1} GEMAT_ptr_split2x2
  (pf_mat | ord, p_mat, lda, i, j) =
  GEMAT_ptr_split2x2_tsz {a1} (pf_mat | ord, p_mat, lda, i, j, sizeof<a1>)
// end of [GEMAT_ptr_split2x2]

(* ****** ****** *)

implement{a}
  GEMAT_row_ptr_allocfree {m,n} (m, n) = let
  val [nm:int] [l:addr] (pf_gc, pf_nm, pf_fmat | p) =
    fmatrix_ptr_alloc<a> (n, m)
  prval () = mul_nat_nat_nat (pf_nm)
  prval (pf_gmat, fpf_fmat) = GEMAT_v_of_fmatrix_v (pf_fmat)
  prval TRANORDcolrow () = GEMAT_v_trans (pf_gmat)
  val free = lam (
    pf_gmat: GEMAT (a?, m, n, row, n) @ l | p: ptr l
  ) : void =<fun,lin> let
    prval TRANORDrowcol () = GEMAT_v_trans (pf_gmat) in
    fmatrix_ptr_free {a} (pf_gc, pf_nm, fpf_fmat {a?} (pf_gmat) | p)
  end // end of [val]
in
  (pf_gmat | p, free)
end // end of [GEMAT_ptr_allocfree]

(* ****** ****** *)

implement{a}
  GEMAT_col_ptr_allocfree {m,n} (m, n) = let
  val [mn:int] [l:addr] (pf_gc, pf_mn, pf_fmat | p) =
    fmatrix_ptr_alloc<a> (m, n)
  prval () = mul_nat_nat_nat (pf_mn)
  prval (pf_gmat, fpf_fmat) = GEMAT_v_of_fmatrix_v (pf_fmat)
  val free = lam (
    pf_gmat: GEMAT (a?, m, n, col, m) @ l | p: ptr l
  ) : void =<fun,lin>
    fmatrix_ptr_free {a} (pf_gc, pf_mn, fpf_fmat {a?} (pf_gmat) | p)
  // end of [val]
in
  (pf_gmat | p, free)
end // end of [GEMAT_col_ptr_allocfree]

(* ****** ****** *)

// X <- alpha
implement{a} GEMAT_ptr_initialize_elt
  {ord} {m,n} {ld} (ord, X, m, n, ld, alpha) = let
  fun loop_row {m,n:nat} {lx:addr} .<m>. (
      pf_gmat: !GEMAT_v (a?, m, n, row, ld, lx)
                 >> GEMAT_v (a, m, n, row, ld, lx)
    | pX: ptr lx, m: size_t m, n: size_t n
    ) :<cloref> void =
    if m > 0 then let
      val (pfX1_gmat, pfX2_gmat, fpf_gmat | pX1, pX2) =
        GEMAT_ptr_split2x1<a?> (pf_gmat | ORDERrow, pX, ld, 1)
      prval (pf2_inc, pfX1_gvec, fpfX1_gmat) =
        GEVEC_v_of_GEMAT_v_row (pfX1_gmat)
      prval MATVECINCrowrow () = pf2_inc
      val () = GEVEC_ptr_initialize_elt<a> (!pX1, n, 1(*incX*), alpha)
      prval () = pfX1_gmat := fpfX1_gmat (pfX1_gvec)
      val () = loop_row (pfX2_gmat | pX2, m-1, n)
      prval () = pf_gmat := fpf_gmat {a} (pfX1_gmat, pfX2_gmat)
    in
      // nothing
    end else let
      prval () = GEMAT_v_unnil_row (pf_gmat)
      prval () = pf_gmat := GEMAT_v_nil_row {a} {row} {n} {ld} {lx} ()
    in
      // nothing
    end // end of [if]
  // end of [loop_row]
in
   case+ ord of
   | ORDERrow () => loop_row (view@ X | &X, m, n)
   | ORDERcol () => let
       prval TRANORDcolrow () =
         GEMAT_v_trans {a?} {col} (view@ X)
       // end of [prval]
       val () = loop_row (view@ X | &X, n, m)
       prval TRANORDrowcol () = GEMAT_v_trans {a} {row} (view@ X)
     in
       // nothing
     end // end of [ORDERcol]
end // end of [GEMAT_ptr_initialize_elt]

(* ****** ****** *)

implement{a} GEMAT_ptr_initialize_fun
  {v} {ord} {m,n} {ld} (pf | ord, X, m, n, ld, f) = () where {
  val _(*ptr*) = __cast (X) where {
    extern castfn __cast
      (X: &GEMAT (a?, m, n, ord, ld) >> GEMAT (a, m, n, ord, ld)):<> ptr
  } // end of [val]
  val () = GEMAT_ptr_iforeach_fun<a> (pf | ord, X, f, ord, m, n, ld)
} // end of [GEMAT_ptr_initialize_fun]

(* ****** ****** *)

implement{a} GEMAT_ptr_copy
  (ord, M1, M2, m, n, ld1, ld2) =
  GEMAT_ptr_copy_tsz (ord, M1, M2, m, n, ld1, ld2, sizeof<a>)
// end of [GEMAT_ptr_copy]

implement GEMAT_ptr_copy_tsz {a}
  {ord} {m,n} {ld1,ld2} (ord, M1, M2, m, n, ld1, ld2, tsz) = let
  fun loop_row {mi,n:nat} {l1,l2:addr} .<mi>. (
      pf1: !GEMAT_v (a, mi, n, row, ld1, l1)
    , pf2: !GEMAT_v (a?, mi, n, row, ld2, l2) >> GEMAT_v (a, mi, n, row, ld2, l2)
    | p1: ptr l1, p2: ptr l2, mi: size_t mi, n: size_t n
    ) :<cloref> void =
    if mi > 0 then let
      val (pf11, pf12, fpf1 | p11, p12) = GEMAT_ptr_split2x1_tsz {a} (pf1 | ORDERrow, p1, ld1, 1, tsz)
      prval (pf1_inc, pf11, fpf11) = GEVEC_v_of_GEMAT_v_row {a} (pf11)
      prval MATVECINCrowrow () = pf1_inc
      prval pf11 = array_v_of_GEVEC_v {a} (pf11)
      val (pf21, pf22, fpf2 | p21, p22) = GEMAT_ptr_split2x1_tsz {a?} (pf2 | ORDERrow, p2, ld2, 1, tsz)
      prval (pf2_inc, pf21, fpf21) = GEVEC_v_of_GEMAT_v_row {a?} (pf21)
      prval MATVECINCrowrow () = pf2_inc
      prval pf21 = array_v_of_GEVEC_v {a?} (pf21)
      val () = array_ptr_copy_tsz {a} (!p11, !p21, n, tsz)
      prval pf11 = GEVEC_v_of_array_v {a} (pf11)
      prval pf11 = fpf11 (pf11)
      prval pf21 = GEVEC_v_of_array_v {a} (pf21)
      prval pf21 = fpf21 (pf21)
      val () = loop_row (pf12, pf22 | p12, p22, mi-1, n)
      prval () = pf1 := fpf1 {a} (pf11, pf12)
      prval () = pf2 := fpf2 {a} (pf21, pf22)
    in
      // nothing
    end else let
      prval () = GEMAT_v_unnil_row (pf2) in pf2 := GEMAT_v_nil_row {a} ()
    end // end of [if]
  // end of [loop_row]
in
  case+ ord of
  | ORDERrow () =>
      loop_row (view@ M1, view@ M2 | &M1, &M2, m, n)
    // end of [ORDERrow]
  | ORDERcol () => let
      prval TRANORDcolrow () = GEMAT_v_trans {a} {col} (view@ M1)
      prval TRANORDcolrow () = GEMAT_v_trans {a?} {col} (view@ M2)
      val () = loop_row (view@ M1, view@ M2 | &M1, &M2, n, m)
      prval TRANORDrowcol () = GEMAT_v_trans {a} {row} (view@ M1)
      prval TRANORDrowcol () = GEMAT_v_trans {a} {row} (view@ M2)
    in
      // nothing
    end // end of [ORDERcol]
end // end of [GEMAT_ptr_copy_tsz]

(* ****** ****** *)

implement
GEMAT_ptr_foreach_fun_tsz__main
  {a} {v} {vt} {ord1,ord2} {m,n} {ld}
  (pf | ord1, M, f, ord2, m, n, ld, tsz, env) = let
  fun loop_row {n > 0}
    {mi:nat | mi <= m} {l:addr} .<mi>. (
    pf: !v
  , pf_mat: !GEMAT_v (a, mi, n, ord1, ld, l)
  | p: ptr l
  , mi: size_t mi
  , env: !vt
  ) :<cloref> void =
  if mi > 0 then let
    val (pf1_mat, pf2_mat, fpf | p1, p2) =
      GEMAT_ptr_split2x1_tsz {a} (pf_mat | ord1, p, ld, 1, tsz)
    prval (pf1_inc, pf1_vec, fpf1_mat) =
      GEVEC_v_of_GEMAT_v_row (pf1_mat)
    val inc = MATVECINC_get (pf1_inc | ORDERrow, ord1, ld)
    val () = GEVEC_ptr_foreach_fun_tsz__main
      {a} {v} (pf | !p1, f, n, inc, tsz, env) // end of [val]
    prval () = pf1_mat := fpf1_mat (pf1_vec)
    val () = loop_row (pf, pf2_mat | p2, mi-1, env)
    prval () = pf_mat := fpf (pf1_mat, pf2_mat)
  in
    // nothing
  end // end of [if]
  fun loop_col {m > 0}
    {ni:nat | ni <= n} {l:addr} .<ni>. (
    pf: !v
  , pf_mat: !GEMAT_v (a, m, ni, ord1, ld, l)
  | p: ptr l
  , ni: size_t ni
  , env: !vt
  ) :<cloref> void =
  if ni > 0 then let
    val (pf1_mat, pf2_mat, fpf | p1, p2) =
      GEMAT_ptr_split1x2_tsz (pf_mat | ord1, p, ld, 1, tsz)
    prval (pf1_inc, pf1_vec, fpf1_mat) =
      GEVEC_v_of_GEMAT_v_col (pf1_mat)
    val inc = MATVECINC_get (pf1_inc | ORDERcol, ord1, ld)
    val () = GEVEC_ptr_foreach_fun_tsz__main
      {a} {v} (pf | !p1, f, m, inc, tsz, env) // end of [val]
    prval () = pf1_mat := fpf1_mat (pf1_vec)
    val () = loop_col (pf, pf2_mat | p2, ni-1, env)
    prval () = pf_mat := fpf (pf1_mat, pf2_mat)
  in
    // nothing
  end // end of [if]
in
  case+ ord2 of
  | ORDERrow () => if n > 0 then let
      val () = loop_row (pf, view@ M | &M, m, env)
    in
      // nothing
    end else begin
      // nothing
    end // end of [ORDERcol]
  | ORDERcol () => if m > 0 then let
      val () = loop_col (pf, view@ M | &M, n, env)
    in
      // nothing
    end else begin
      // nothing
    end // end of [ORDERcol]
end (* end of [GEMAT_ptr_foreach_fun_tsz__main] *)

(* ****** ****** *)

implement{a} GEMAT_ptr_foreach_fun
  {v} {ord1,ord2} {m,n}
  (pf | ord1, base, f, ord2, m, n, ld) = let
  val f = coerce (f) where {
    extern castfn coerce
      (f: (!v | &a) -<> void):<> (!v | &a, !ptr) -<> void
  } // end of [where]
in
  GEMAT_ptr_foreach_fun_tsz__main
    (pf | ord1, base, f, ord2, m, n, ld, sizeof<a>, null)
end // end of [GEMAT_ptr_foreach_fun_tsz]

implement{a} GEMAT_ptr_foreach_clo
  {v} {ord1,ord2} {m,n}
  (pf_v | ord1, M, f, ord2, m, n, ld) = let
  viewtypedef clo_t = (!v | &a) -<clo> void
  stavar l_f: addr
  val p_f: ptr l_f = &f
  viewdef V = @(v, clo_t @ l_f)
  fn app (pf: !V | x: &a, p_f: !ptr l_f):<> void = let
    prval (pf1, pf2) = pf; val () = !p_f (pf1 | x) in pf := (pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = GEMAT_ptr_foreach_fun_tsz__main
    {a} {V} {ptr l_f} (pf | ord1, M, app, ord2, m, n, ld, sizeof<a>, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [GEMAT_ptr_foreach_clo_tsz]

(* ****** ****** *)

implement
GEMAT_ptr_iforeach_fun_tsz__main
  {a} {v} {vt} {ord1,ord2} {m,n} {ld}
  (pf | ord1, M, f, ord2, m, n, ld, tsz, env) = let
  fun loop_row {n > 0}
    {mi:nat | mi <= m} {l:addr} .<mi>. (
    pf: !v
  , pf_mat: !GEMAT_v (a, mi, n, ord1, ld, l)
  | p: ptr l
  , mi: size_t mi
  , env: !vt
  ) :<cloref> void =
  if mi > 0 then let
    val (pf1_mat, pf2_mat, fpf | p1, p2) =
      GEMAT_ptr_split2x1_tsz {a} (pf_mat | ord1, p, ld, 1, tsz)
    prval (pf1_inc, pf1_vec, fpf1_mat) =
      GEVEC_v_of_GEMAT_v_row (pf1_mat)
    val inc = MATVECINC_get (pf1_inc | ORDERrow, ord1, ld)
    val () = GEVEC_ptr_iforeach_clo_tsz__main
      {a} {v} (pf | !p1, !p_clo, n, inc, tsz, env) where {
      val i = m - mi
      var !p_clo = @lam
        (pf: !v | j: sizeLt n, x: &a, env: !vt): void =<clo> f (pf | i, j, x, env)
      // end of [var]
    } // end of [val]
    prval () = pf1_mat := fpf1_mat (pf1_vec)
    val () = loop_row (pf, pf2_mat | p2, mi-1, env)
    prval () = pf_mat := fpf (pf1_mat, pf2_mat)
  in
    // nothing
  end // end of [if]
  fun loop_col {m > 0}
    {nj:nat | nj <= n} {l:addr} .<nj>. (
    pf: !v
  , pf_mat: !GEMAT_v (a, m, nj, ord1, ld, l)
  | p: ptr l
  , nj: size_t nj
  , env: !vt
  ) :<cloref> void =
  if nj > 0 then let
    val (pf1_mat, pf2_mat, fpf | p1, p2) =
      GEMAT_ptr_split1x2_tsz (pf_mat | ord1, p, ld, 1, tsz)
    prval (pf1_inc, pf1_vec, fpf1_mat) =
      GEVEC_v_of_GEMAT_v_col (pf1_mat)
    val inc = MATVECINC_get (pf1_inc | ORDERcol, ord1, ld)
    val () = GEVEC_ptr_iforeach_clo_tsz__main
      {a} {v} (pf | !p1, !p_clo, m, inc, tsz, env) where {
      val j = n-nj
      var !p_clo = @lam
        (pf: !v | i: sizeLt m, x: &a, env: !vt): void =<clo> f (pf | i, j, x, env)
      // end of [var]
    } // end of [val]
    prval () = pf1_mat := fpf1_mat (pf1_vec)
    val () = loop_col (pf, pf2_mat | p2, nj-1, env)
    prval () = pf_mat := fpf (pf1_mat, pf2_mat)
  in
    // nothing
  end // end of [if]
in
  case+ ord2 of
  | ORDERrow () => if n > 0 then let
      val () = loop_row (pf, view@ M | &M, m, env)
    in
      // nothing
    end else begin
      // nothing
    end // end of [ORDERcol]
  | ORDERcol () => if m > 0 then let
      val () = loop_col (pf, view@ M | &M, n, env)
    in
      // nothing
    end else begin
      // nothing
    end // end of [ORDERcol]
end (* end of [GEMAT_ptr_iforeach_fun_tsz__main] *)

(* ****** ****** *)

implement{a} GEMAT_ptr_iforeach_fun
  {v} {ord1,ord2} {m,n}
  (pf | ord1, base, f, ord2, m, n, ld) = let
  val f = coerce (f) where {
    extern castfn coerce
      (f: (!v | sizeLt m, sizeLt n, &a) -<> void)
      :<> (!v | sizeLt m, sizeLt n, &a, !ptr) -<> void
  } // end of [where]
in
  GEMAT_ptr_iforeach_fun_tsz__main
    (pf | ord1, base, f, ord2, m, n, ld, sizeof<a>, null)
end // end of [GEMAT_ptr_iforeach_fun_tsz]

(* ****** ****** *)

implement{a} GEMAT_ptr_iforeach_clo
  {v} {ord1,ord2} {m,n}
  (pf_v | ord1, M, f, ord2, m, n, ld) = let
  viewtypedef clo_t = (!v | sizeLt m, sizeLt n, &a) -<clo> void
  stavar l_f: addr
  val p_f: ptr l_f = &f
  viewdef V = @(v, clo_t @ l_f)
  fn app (
      pf: !V
    | i: sizeLt m, j: sizeLt n, x: &a, p_f: !ptr l_f
    ) :<> void = let
    prval (pf1, pf2) = pf; val () = !p_f (pf1 | i, j, x) in pf := (pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = GEMAT_ptr_iforeach_fun_tsz__main
    {a} {V} {ptr l_f} (pf | ord1, M, app, ord2, m, n, ld, sizeof<a>, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [GEMAT_ptr_iforeach_clo_tsz]

(* ****** ****** *)

//
// TRiangular MATrix representation (part of GEMAT)
//

(* ****** ****** *)

local

fn{a:t@ype}
  TRMAT_ptr_get_elt_at_dummy {ord:order} {l:addr} (
    ord: ORDER ord, p_mat: ptr l, lda: size_t, i: size_t, j: size_t
  ) :<> a = let
  val ofs = (case+ ord of
    | ORDERrow () => (i szmul lda + j) * sizeof<a>
    | ORDERcol () => (i + j szmul lda) * sizeof<a>
  ) : size_t
  val [ofs:int] ofs = sz2sz (ofs)
  prval (pf, fpf) = __lemma () where {
    extern prfun __lemma (): (a @ l+ofs, a @ l+ofs -<lin> void)
  } // end of [prval]
  val x = !(p_mat + ofs)
  prval () = fpf (pf)
in
  x
end // end of [TRMAT_ptr_get_elt_at_dummy]

fn{a:t@ype}
  TRMAT_ptr_set_elt_at_dummy {ord:order} {l:addr} (
    ord: ORDER ord, p_mat: ptr l, lda: size_t, i: size_t, j: size_t, x: a
  ) :<> void = let
  val ofs = (case+ ord of
    | ORDERrow () => (i szmul lda + j) * sizeof<a>
    | ORDERcol () => (i + j szmul lda) * sizeof<a>
  ) : size_t
  val [ofs:int] ofs = sz2sz (ofs)
  prval (pf, fpf) = __lemma () where {
    extern prfun __lemma (): (a @ l+ofs, a @ l+ofs -<lin> void)
  } // end of [prval]
  val x = !(p_mat + ofs) := x
  prval () = fpf (pf)
in
  // nothing
end // end of [TRMAT_ptr_get_elt_at_dummy]

in // in of [local]

implement{a} TRMAT_UN_ptr_get_elt_at
  (ord, A, lda, i, j) = TRMAT_ptr_get_elt_at_dummy<a> (ord, &A, lda, i, j)
// end of [TRMAT_UN_ptr_get_elt_at]

implement{a} TRMAT_UN_ptr_set_elt_at
  (ord, A, lda, i, j, x) = TRMAT_ptr_set_elt_at_dummy<a> (ord, &A, lda, i, j, x)
// end of [TRMAT_UN_ptr_set_elt_at]

implement{a} TRMAT_UU_ptr_get_elt_at
  (ord, A, lda, i, j) = TRMAT_ptr_get_elt_at_dummy<a> (ord, &A, lda, i, j)
// end of [TRMAT_UU_ptr_get_elt_at]

implement{a} TRMAT_UU_ptr_set_elt_at
  (ord, A, lda, i, j, x) = TRMAT_ptr_set_elt_at_dummy<a> (ord, &A, lda, i, j, x)
// end of [TRMAT_UU_ptr_set_elt_at]

implement{a} TRMAT_LN_ptr_get_elt_at
  (ord, A, lda, i, j) = TRMAT_ptr_get_elt_at_dummy<a> (ord, &A, lda, i, j)
// end of [TRMAT_LN_ptr_get_elt_at]

implement{a} TRMAT_LN_ptr_set_elt_at
  (ord, A, lda, i, j, x) = TRMAT_ptr_set_elt_at_dummy<a> (ord, &A, lda, i, j, x)
// end of [TRMAT_LN_ptr_set_elt_at]

implement{a} TRMAT_LU_ptr_get_elt_at
  (ord, A, lda, i, j) = TRMAT_ptr_get_elt_at_dummy<a> (ord, &A, lda, i, j)
// end of [TRMAT_LU_ptr_get_elt_at]

implement{a} TRMAT_LU_ptr_set_elt_at
  (ord, A, lda, i, j, x) = TRMAT_ptr_set_elt_at_dummy<a> (ord, &A, lda, i, j, x)
// end of [TRMAT_LU_ptr_set_elt_at]

end // end of [local]

(* ****** ****** *)

extern fun TRMAT_U_ptr_split2x2_tsz
  {a1:viewt@ype} 
  {ord:order} {dg:diag} {m,i:nat | i <= m}
  {lda:inc} {l0:addr} (
    pf_mat: TRMAT_v (a1, m, ord, upper, dg, lda, l0)
  | ord: ORDER ord, A: ptr l0, lda: size_t lda, i: size_t i, tsz: sizeof_t a1
  ) :<> TRMAT_U_ptr_split2x2_res_t (a1, m, i, ord, dg, lda, l0)

implement TRMAT_U_ptr_split2x2_tsz
  {a1} {ord} {dg} {m,i} {lda} {l0}
  (pf_mat | ord, p_mat, lda, i, tsz) = let
  val res = (case+ ord of
    | ORDERrow () => let
        val i_tmp = sz2sz (i * tsz) // no-op casting
        val p_tmp = p_mat + sz2sz ((i * lda) szmul tsz)
      in @(
        unit_v, unit_v, unit_v, unit_p | p_mat, p_mat + i_tmp, p_tmp + i_tmp
      ) end // end of [ORDERrow]
    | ORDERcol () => let
        val i_tmp = sz2sz (i * tsz) // no-op casting
        val p_tmp = p_mat + sz2sz ((i * lda) szmul tsz)
      in @(
        unit_v, unit_v, unit_v, unit_p | p_mat, p_tmp, p_tmp + i_tmp
      ) end // end of [ORDERcol]
  ) : (unit_v, unit_v, unit_v, unit_p | ptr, ptr, ptr)
  extern castfn __cast {vt:viewt@ype}
    (pf: TRMAT_v (a1, m, ord, upper, dg, lda, l0) | res: vt)
    :<> TRMAT_U_ptr_split2x2_res_t (a1, m, i, ord, dg, lda, l0)
  // end of [__cast]
in
  __cast (pf_mat | res)
end // end of [TRMAT_U_ptr_split2x2_tsz]

implement{a1}
  TRMAT_U_ptr_split2x2 (pf_mat | ord, A, lda, i) =
  TRMAT_U_ptr_split2x2_tsz (pf_mat | ord, A, lda, i, sizeof<a1>)
// end of [TRMAT_U_ptr_split2x2]

(* ****** ****** *)

extern fun TRMAT_L_ptr_split2x2_tsz
  {a1:viewt@ype}
  {ord:order} {dg:diag} {m,i:nat | i <= m}
  {lda:inc} {l0:addr} (
    pf_mat: TRMAT_v (a1, m, ord, lower, dg, lda, l0)
  | ord: ORDER ord, A: ptr l0, lda: size_t lda, i: size_t i, tsz: sizeof_t a1
  ) :<> TRMAT_L_ptr_split2x2_res_t (a1, m, i, ord, dg, lda, l0)

implement TRMAT_L_ptr_split2x2_tsz
  {a1} {ord} {dg} {m,i} {lda} {l0}
  (pf_mat | ord, p_mat, lda, i, tsz) = let
  val res = (case ord of
    | ORDERrow () => let
        val i_tmp = sz2sz (i * tsz) // no-op casting
        val p_tmp = p_mat + sz2sz ((i * lda) szmul tsz)
      in @(
        unit_v, unit_v, unit_v, unit_p | p_mat, p_tmp, p_tmp + i_tmp
      ) end // end of [ORDERrow]
    | ORDERcol () => let
        val i_tmp = sz2sz (i * tsz) // no-op casting
        val p_tmp = p_mat + sz2sz ((i * lda) szmul tsz)
      in @(
        unit_v, unit_v, unit_v, unit_p | p_mat, p_mat + i_tmp, p_tmp + i_tmp
      ) end // end of [ORDERcol]
  ) : (unit_v, unit_v, unit_v, unit_p | ptr, ptr, ptr)
  extern castfn __cast {vt:viewt@ype}
    (pf: TRMAT_v (a1, m, ord, lower, dg, lda, l0) | res: vt)
    :<> TRMAT_L_ptr_split2x2_res_t (a1, m, i, ord, dg, lda, l0)
  // end of [__cast]
in
  __cast (pf_mat | res)
end // end of [TRMAT_L_ptr_split2x2_tsz]

implement{a1}
  TRMAT_L_ptr_split2x2 (pf_mat | ord, A, lda, i) =
  TRMAT_L_ptr_split2x2_tsz (pf_mat | ord, A, lda, i, sizeof<a1>)
// end of [TRMAT_L_ptr_split2x2]

(* ****** ****** *)

extern
prfun TRMAT1x1_v_takeout_unit
  {a1:viewt@ype}
  {ord:order} {ul:uplo} {ld:inc} {l:addr} (
    pf: TRMAT_v (a1, 1, ord, ul, unit, ld, l)
  ) : (
    {a2:viewt@ype | a1 \tszeq a2} () -<prf> TRMAT_v (a2, 1, ord, ul, unit, ld, l)
  )
// end of [TRMAT1x1_v_takeout_unit]

extern
prfun TRMAT1x1_v_takeout_nonunit
  {a1:viewt@ype}
  {ord:order} {ul:uplo} {ld:inc} {l:addr} (
    pf: TRMAT_v (a1, 1, ord, ul, nonunit, ld, l)
  ) : (
    a1 @ l
  , {a2:viewt@ype | a1 \tszeq a2} a2 @ l -<prf> TRMAT_v (a2, 1, ord, ul, nonunit, ld, l)
  )
// end of [TRMAT1x1_v_takeout_nonunit]

(* ****** ****** *)

implement{a} TRMAT_ptr_copy
  (ord, ul, dg, M1, M2, m, ld1, ld2) =
  TRMAT_ptr_copy_tsz (ord, ul, dg, M1, M2, m, ld1, ld2, sizeof<a>)
// end of [TRMAT_ptr_copy]

(*
implement TRMAT_ptr_copy_tsz
  {a} {ord} {ul} {dg} {m} {ld1,ld2}
  (ord, ul, dg, M1, M2, m, ld1, ld2, tsz) = let
  fun loop_row_upper_nonunit
    {mi:nat} {l1,l2:addr} .<mi>. (
      pf1: !TRMAT_v (a, mi, row, upper, nonunit, ld1, l1)
    , pf2: !TRMAT_v (a?, mi, row, upper, nonunit, ld2, l2)
         >> TRMAT_v (a, mi, row, upper, nonunit, ld2, l2)
    | p1: ptr l1, p2: ptr l2, mi: size_t mi
    ) :<cloref> void =
    if mi > 0 then let
      val (pf11, pf12, pf13, fpf1 | p11, p12, p13) = 
        TRMAT_U_ptr_split2x2 (pf1 | ORDERrow, p1, ld1, 1)
      val (pf21, pf22, pf23, fpf2 | p21, p22, p23) = 
        TRMAT_U_ptr_split2x2 (pf2 | ORDERrow, p2, ld2, 1)
//
      prval (pf11, fpf11) = TRMAT1x1_v_takeout_nonunit {a} (pf11)
      prval (pf21, fpf21) = TRMAT1x1_v_takeout_nonunit {a?} (pf21)
      val () = !p21 := !p11
      prval pf11 = fpf11 (pf11)
      prval pf21 = fpf21 (pf21)
//
      prval (pf12_inc, pf12, fpf12) = GEVEC_v_of_GEMAT_v_row {a} (pf12)
      prval MATVECINCrowrow () = pf12_inc
      prval pf12 = array_v_of_GEVEC_v {a} (pf12)
      prval (pf22_inc, pf22, fpf22) = GEVEC_v_of_GEMAT_v_row {a?} (pf22)
      prval MATVECINCrowrow () = pf22_inc
      prval pf22 = array_v_of_GEVEC_v {a?} (pf22)
      val () = array_ptr_copy_tsz {a} (!p12, !p22, mi - 1, tsz)
      prval pf12 = GEVEC_v_of_array_v {a} (pf12)
      prval pf12 = fpf12 {a} (pf12)
      prval pf22 = GEVEC_v_of_array_v {a} (pf22)
      prval pf22 = fpf22 {a} (pf22)
//
      val () = loop_row_upper_nonunit (pf13, pf23 | p13, p23, mi - 1)
//
      prval () = pf1 := fpf1 {a} (pf11, pf12, pf13)
      prval () = pf2 := fpf2 {a} (pf21, pf22, pf23)
    in
      // nothing
    end else let
      prval () = TRMAT_v_unnil (pf2) in pf2 := TRMAT_v_nil {a} ()
    end // end of [if]
  // end of [loop_row_upper_nonunit]

  fun loop_row_lower_nonunit
    {mi:nat} {l1,l2:addr} .<mi>. (
      pf1: !TRMAT_v (a, mi, row, lower, nonunit, ld1, l1)
    , pf2: !TRMAT_v (a?, mi, row, lower, nonunit, ld2, l2)
         >> TRMAT_v (a, mi, row, lower, nonunit, ld2, l2)
    | p1: ptr l1, p2: ptr l2, mi: size_t mi
    ) :<cloref> void =
    if mi > 0 then let
      val (pf11, pf12, pf13, fpf1 | p11, p12, p13) = 
        TRMAT_L_ptr_split2x2 (pf1 | ORDERrow, p1, ld1, mi-1)
      val (pf21, pf22, pf23, fpf2 | p21, p22, p23) = 
        TRMAT_L_ptr_split2x2 (pf2 | ORDERrow, p2, ld2, mi-1)
//
      prval (pf13, fpf13) = TRMAT1x1_v_takeout_nonunit {a} (pf13)
      prval (pf23, fpf23) = TRMAT1x1_v_takeout_nonunit {a?} (pf23)
      val () = !p23 := !p13
      prval pf13 = fpf13 (pf13)
      prval pf23 = fpf23 (pf23)
//
      prval (pf12_inc, pf12, fpf12) = GEVEC_v_of_GEMAT_v_row {a} (pf12)
      prval MATVECINCrowrow () = pf12_inc
      prval pf12 = array_v_of_GEVEC_v {a} (pf12)
      prval (pf22_inc, pf22, fpf22) = GEVEC_v_of_GEMAT_v_row {a?} (pf22)
      prval MATVECINCrowrow () = pf22_inc
      prval pf22 = array_v_of_GEVEC_v {a?} (pf22)
      val () = array_ptr_copy_tsz {a} (!p12, !p22, mi - 1, tsz)
      prval pf12 = GEVEC_v_of_array_v {a} (pf12)
      prval pf12 = fpf12 {a} (pf12)
      prval pf22 = GEVEC_v_of_array_v {a} (pf22)
      prval pf22 = fpf22 {a} (pf22)
//
      val () = loop_row_lower_nonunit (pf11, pf21 | p11, p21, mi - 1)
//
      prval () = pf1 := fpf1 {a} (pf11, pf12, pf13)
      prval () = pf2 := fpf2 {a} (pf21, pf22, pf23)
    in
      // nothing
    end else let
      prval () = TRMAT_v_unnil (pf2) in pf2 := TRMAT_v_nil {a} ()
    end // end of [if]
  // end of [loop_row_upper_nonunit]
in
  case+ dg of
  | DIAGnonunit () => begin case+ ord of
    | ORDERrow () => begin case+ ul of
      | UPLOupper () => loop_row_upper_nonunit (view@ M1, view@ M2 | &M1, &M2, m)
      | UPLOlower () => loop_row_lower_nonunit (view@ M1, view@ M2 | &M1, &M2, m)
      end // end of [ORDERrow]
    | ORDERcol () => let
        prval (pf1_order, pf1_uplo) = TRMAT_v_trans (view@ M1)
        prval TRANORDcolrow () = pf1_order
        prval (pf2_order, pf2_uplo) = TRMAT_v_trans (view@ M2)
        prval TRANORDcolrow () = pf2_order
      in
        case+ ul of
        | UPLOupper () => let
            prval TRANUPLOupperlower () = pf1_uplo
            prval TRANUPLOupperlower () = pf2_uplo
            val () = loop_row_lower_nonunit (view@ M1, view@ M2 | &M1, &M2, m)
            prval (pf1_order, pf1_uplo) = TRMAT_v_trans (view@ M1)
            prval TRANORDrowcol () = pf1_order
            prval TRANUPLOlowerupper () = pf1_uplo
            prval (pf2_order, pf2_uplo) = TRMAT_v_trans (view@ M2)
            prval TRANORDrowcol () = pf2_order
            prval TRANUPLOlowerupper () = pf2_uplo
          in
            // nothing
          end // end of [UPLOupper]
        | UPLOlower () => let
            prval TRANUPLOlowerupper () = pf1_uplo
            prval TRANUPLOlowerupper () = pf2_uplo
            val () = loop_row_upper_nonunit (view@ M1, view@ M2 | &M1, &M2, m)
            prval (pf1_order, pf1_uplo) = TRMAT_v_trans (view@ M1)
            prval TRANORDrowcol () = pf1_order
            prval TRANUPLOupperlower () = pf1_uplo
            prval (pf2_order, pf2_uplo) = TRMAT_v_trans (view@ M2)
            prval TRANORDrowcol () = pf2_order
            prval TRANUPLOupperlower () = pf2_uplo
          in
            // nothing
          end
      end // end of [ORDERcol]
    end // end of [DIAGnonunit]
  | DIAGunit () =>
      if m > 0 then let
        val (pf1, fpf1 | p1) = TRMAT_ptr_unit_nonunit<a> (view@ M1 | ord, &M1, ld1)
        val (pf2, fpf2 | p2) = TRMAT_ptr_unit_nonunit<a?> (view@ M2 | ord, &M2, ld2)
        val () = TRMAT_ptr_copy_tsz (ord, ul, DIAGnonunit, !p1, !p2, m-1, ld1, ld2, tsz)
        prval () = view@ M1 := fpf1 {a} (pf1)
        prval () = view@ M2 := fpf2 {a} (pf2)
      in
        // nothing
      end else let
        prval () = TRMAT_v_unnil (view@ M2) in view@ M2 := TRMAT_v_nil {a} ()
      end // end of [if]
   // end of [DIAGunit]
end // end of [TRMAT_ptr_copy_tsz]
*)

(* ****** ****** *)

(* end of [genarrays.dats] *)
