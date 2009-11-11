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

#define szmul mul_size_size

(* ****** ****** *)

implement{a} GEVEC_ptr_takeout
  {n} {d} {l0} (pf_vec | p_vec, d, i) = let
  viewdef V0 = GEVEC_v (a, n, d, l0)
  val ofs = i \szmul (d \szmul sizeof<a>)
  val [ofs:int] ofs = size1_of_size (ofs) // no-op casting
  stadef l = l0 + ofs
  prval (pf_at, fpf_vec) = __cast (pf_vec) where {
    extern prfun __cast (pf: V0): (a @ l, a @ l -<lin,prf> V0)
  }
in
  #[l | (pf_at, fpf_vec | p_vec + ofs) ]
end // end of [GEVEC_ptr_takeout]

(* ****** ****** *)

implement{a1} GEVEC_ptr_split
  {n,i} {d} {l0} (pf_vec | p_vec, d, i) = let
  viewdef V0 (a: viewt@ype) = GEVEC_v (a, n, d, l0)
  val ofs = i \szmul (d \szmul sizeof<a1>)
  val [ofs:int] ofs = size1_of_size (ofs) // no-op casting
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
  {m,n} {ord} {lda} {l0} (pf_mat | ord, p_mat, lda, i, j) = let
  viewdef V0 = GEMAT_v (a, m, n, ord, lda, l0)
  val ofs = (case+ ord of
    | ORDERrow () => (i \szmul lda + j) * sizeof<a> | ORDERcol () => (i + j \szmul lda) * sizeof<a>
  ) : size_t
  val [ofs:int] ofs = size1_of_size (ofs)
  stadef l = l0 + ofs
  prval (pf_at, fpf_mat) = __cast (pf_mat) where {
    extern prfun __cast (pf: V0): (a @ l, a @ l -<lin,prf> V0)
  }
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
  {m,n} {ord} {lda} {l0} (pf_mat | ord, p_mat, lda) = let
  viewdef V0 = GEMAT_v (a, m, n, ord, lda, l0)
  val ofs = (case+ ord of
    | ORDERrow () => lda * sizeof<a> | ORDERcol () => sizeof<a>
  ) : size_t // end of [val]
  val [ofs:int] ofs = size1_of_size (ofs)
  stadef l = l0 + ofs
  viewdef V1 = GEMAT_v (a, m-1, n, ord, lda, l)
  prval (pf1_mat, fpf_mat) = __cast (pf_mat) where {
    extern prfun __cast (pf: V0): (V1, V1 -<lin,prf> V0)
  }
in
  #[l | (pf1_mat, fpf_mat | p_mat + ofs) ]
end // end of [GEMAT_ptr_tail_row]

(* ****** ****** *)

implement{a} GEMAT_ptr_tail_col
  {m,n} {ord} {lda} {l0} (pf_mat | ord, p_mat, lda) = let
  viewdef V0 = GEMAT_v (a, m, n, ord, lda, l0)
  val ofs = (case+ ord of
    | ORDERrow () => sizeof<a> | ORDERcol () => lda * sizeof<a>
  ) : size_t // end of [val]
  val [ofs:int] ofs = size1_of_size (ofs)
  stadef l = l0 + ofs
  viewdef V1 = GEMAT_v (a, m, n-1, ord, lda, l)
  prval (pf1_mat, fpf_mat) = __cast (pf_mat) where {
    extern prfun __cast (pf: V0): (V1, V1 -<lin,prf> V0)
  }
in
  #[l | (pf1_mat, fpf_mat | p_mat + ofs) ]
end // end of [GEMAT_ptr_tail_col]

(* ****** ****** *)

(*
** The following function acts as a dummy for [GEMAT_ptr_split1x2_tsz]
*)
extern fun
GEMAT_ptr_split1x2_tsz_dummy
  {a:viewt@ype} {m,n:nat}
  {j:nat | j <= n} {ord:order} {lda:pos} {l0:addr} (
    pf_mat: unit_v // GEMAT_v (a, m, n, ord, lda, l0)
  | ord: ORDER ord
  , p_mat: ptr l0
  , lda: size_t lda
  , j: size_t j
  , tsz: sizeof_t a
  ) :<> [l1,l2:addr] @(
    unit_v // GEMAT_v (a, m, j, ord, lda, l1)  
  , unit_v // GEMAT_v (a, m, n-j, ord, lda, l2)
  , unit_p // (GEMAT_v (a, m, j, ord, lda, l1),
           //  GEMAT_v (a, m, n-j, ord, lda, l2)
           // ) -<prf> GEMAT_v (a, m, n, ord, lda, l0)
  | ptr l1, ptr l2
  ) = "atslib_GEMAT_ptr_split1x2_tsz"

implement
  GEMAT_ptr_split1x2_tsz_dummy
  (pf_mat | ord, p_mat, lda, j, tsz) = let
  prval unit_v () = pf_mat
  val ofs = (case ord of
    | ORDERrow () => j \szmul tsz | ORDERcol () => j \szmul (lda * tsz)
  ) : size_t // end of [val]
  val ofs = size1_of_size (ofs)
in
  (unit_v, unit_v, unit_p | p_mat, p_mat + ofs)
end // end of [GEMAT_ptr_split1x2_tsz_dummy]

(* ****** ****** *)

(*
** The following function acts as a dummy for [GEMAT_ptr_split2x1_tsz]
*)
extern fun
GEMAT_ptr_split2x1_tsz_dummy
  {a:viewt@ype} {m,n:nat}
  {i:nat | i <= m} {ord:order} {lda:pos} {l0:addr} (
    pf_mat: unit_v // GEMAT_v (a, m, n, ord, lda, l0)
  | ord: ORDER ord
  , p_mat: ptr l0
  , lda: size_t lda
  , i: size_t i
  , tsz: sizeof_t a
  ) :<> [l1,l2:addr] @(
    unit_v // GEMAT_v (a, i, n, ord, lda, l1)  
  , unit_v // GEMAT_v (a, m-i, n, ord, lda, l2)
  , unit_p // (GEMAT_v (a, i, n, ord, lda, l1),
           //  GEMAT_v (a, m-i, n, ord, lda, l2)
           // ) -<prf> GEMAT_v (a, m, n, ord, lda, l0)
  | ptr l1, ptr l2
  ) = "atslib_GEMAT_ptr_split2x1_tsz"

implement
  GEMAT_ptr_split2x1_tsz_dummy
  (pf_mat | ord, p_mat, lda, i, tsz) = let
  prval unit_v () = pf_mat
  val ofs = (case ord of
    | ORDERrow () => i \szmul (lda * tsz) | ORDERcol () => i \szmul tsz
  ) : size_t // end of [val]
  val ofs = size1_of_size (ofs)
in
  (unit_v, unit_v, unit_p | p_mat, p_mat + ofs)
end // end of [GEMAT_ptr_split1x2_tsz_dummy]

(* ****** ****** *)

(*
** The following function acts as a dummy for [GEMAT_ptr_split2x2_tsz]
*)
extern fun
GEMAT_ptr_split2x2_tsz_dummy
  {a:viewt@ype}
  {m,n:nat} {i,j:nat | i <= m; j <= n}
  {ord:order} {lda:pos} {l0:addr} (
    pf_mat: unit_v // GEMAT_v (a, m, n, ord, lda, l0)
  | ord: ORDER ord
  , p_mat: ptr l0
  , lda: size_t lda, i: size_t i, j: size_t j
  , tsz: sizeof_t a
  ) :<> [l11,l12,l21,l22:addr] @(
    unit_v // GEMAT_v (a, i, j, ord, lda, l11)  
  , unit_v // GEMAT_v (a, i, n-j, ord, lda, l12)
  , unit_v // GEMAT_v (a, m-i, j, ord, lda, l21)
  , unit_v // GEMAT_v (a, m-i, n-j, ord, lda, l22)
  , unit_p // (GEMAT_v (a, i, j, ord, lda, l11),
           //  GEMAT_v (a, i, n-j, ord, lda, l12),
           //  GEMAT_v (a, m-i, j, ord, lda, l21),
           //  GEMAT_v (a, m-i, n-j, ord, lda, l22)
           // ) -<prf> GEMAT_v (a, m, n, ord, lda, l0)
   | ptr l11 // l11 should equal l0
   , ptr l12
   , ptr l21
   , ptr l22
   ) = "atslib_GEMAT_ptr_split2x2_tsz"
// end of [GEMAT_ptr_split2x2_tsz]

implement
  GEMAT_ptr_split2x2_tsz_dummy (
    pf_mat | ord, p_mat, lda, i, j, tsz
  ) = let
  prval unit_v () = pf_mat
in
  case+ ord of
  | ORDERrow () => let
      val i_tmp = size1_of_size (j * tsz) // no-op casting
      val p_tmp = p_mat + size1_of_size ((i \szmul lda) \szmul tsz)
    in @(
      unit_v, unit_v, unit_v, unit_v, unit_p
    | p_mat, p_mat + i_tmp, p_tmp, p_tmp + i_tmp
    ) end // end of [ORDERrow]
  | ORDERcol () => let
      val i_tmp = size1_of_size (i * tsz) // no-op casting
      val p_tmp = p_mat + size1_of_size ((j \szmul lda) \szmul tsz)
    in @(
      unit_v, unit_v, unit_v, unit_v, unit_p
    | p_mat, p_tmp, p_mat + i_tmp, p_tmp + i_tmp
    ) end // end of [ORDERcol]
end // end of [GEMAT_ptr_split2x2_tsz_dummy]

(* ****** ****** *)

extern
fun GEMAT_ptr_split1x2_tsz {a1:viewt@ype}
  {m,n:nat} {j:nat | j <= n} {ord:order} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a1, m, n, ord, lda, l0)
  | ord: ORDER ord, p_mat: ptr l0, lda: size_t lda, j: size_t j, tsz: sizeof_t a1
  ) :<> GEMAT_ptr_split1x2_res_t (a1, m, n, j, ord, lda, l0)
    = "atslib_GEMAT_ptr_split1x2_tsz"
(* end of [GEMAT_ptr_split1x2_tsz] *)

extern
fun GEMAT_ptr_split2x1_tsz {a1:viewt@ype}
  {m,n:nat} {i:nat | i <= m} {ord:order} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a1, m, n, ord, lda, l0)
  | ord: ORDER ord, p_mat: ptr l0, lda: size_t lda, i: size_t i, tsz: sizeof_t a1
  ) :<> GEMAT_ptr_split2x1_res_t (a1, m, n, i, ord, lda, l0)
    = "atslib_GEMAT_ptr_split2x1_tsz"
(* end of [GEMAT_ptr_split2x1_tsz] *)

extern
fun GEMAT_ptr_split2x2_tsz {a1:viewt@ype}
  {m,n:nat} {i,j:nat | i <= m; j <= n} {ord:order} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a1, m, n, ord, lda, l0)
  | ord: ORDER ord, p_mat: ptr l0, lda: size_t lda, i: size_t i, j: size_t j, tsz: sizeof_t a1
  ) :<> GEMAT_ptr_split2x2_res_t (a1, m, n, i, j, ord, lda, l0)
  = "atslib_GEMAT_ptr_split2x2_tsz"
// end of [GEMAT_ptr_split2x2_tsz]

implement{a1} GEMAT_ptr_split1x2
  (pf_mat | ord, p_mat, lda, j) =
  GEMAT_ptr_split1x2_tsz {a1} (pf_mat | ord, p_mat, lda, j, sizeof<a1>)
// end of [GEMAT_ptr_split1x2]

implement{a1} GEMAT_ptr_split2x1
  (pf_mat | ord, p_mat, lda, i) =
  GEMAT_ptr_split2x1_tsz {a1} (pf_mat | ord, p_mat, lda, i, sizeof<a1>)
// end of [GEMAT_ptr_split2x1]

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
        GEVEC_v_of_GEMAT_v_row (pfX1_gmat, ORDERrow, ld)
      prval MATVECINCrowrow () = pf2_inc
      val () = GEVEC_ptr_initialize_elt<a> (!pX1, n, 1(*incX*), alpha)
      prval () = pfX1_gmat := fpfX1_gmat (pfX1_gvec)
      val () = loop_row (pfX2_gmat | pX2, m-1, n)
      prval () = pf_gmat := fpf_gmat {a} (pfX1_gmat, pfX2_gmat)
    in
      // nothing
    end else let
      prval () = GEMAT_v_row_unnil (pf_gmat)
      prval () = pf_gmat := GEMAT_v_row_nil {a} {n} {row} {ld} {lx} ()
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
      GEMAT_ptr_split2x1_tsz (pf_mat | ord1, p, ld, 1, tsz)
    prval (pf1_inc, pf1_vec, fpf1_mat) =
      GEVEC_v_of_GEMAT_v_row (pf1_mat, ord1, ld)
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
      GEVEC_v_of_GEMAT_v_col (pf1_mat, ord1, ld)
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
      GEMAT_ptr_split2x1_tsz (pf_mat | ord1, p, ld, 1, tsz)
    prval (pf1_inc, pf1_vec, fpf1_mat) =
      GEVEC_v_of_GEMAT_v_row (pf1_mat, ord1, ld)
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
      GEVEC_v_of_GEMAT_v_col (pf1_mat, ord1, ld)
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

(*
** The following function acts as a dummy for [TRMAT_ptr_split2x2_tsz]
*)
extern fun
TRMAT_ptr_split2x2_tsz_dummy
  {a:viewt@ype} {m:nat} {i:nat | i <= m}
  {ord:order} {ul:uplo} {dg:diag} {lda:pos} {l0:addr} (
    pf_mat: unit_v // TRMAT_v (a, m, ord, ul, dg, lda, l0)
  | ord: ORDER ord
  , ul: UPLO ul
  , p_mat: ptr l0
  , lda: size_t lda, i: size_t i
  , tsz: sizeof_t a
  ) :<> @(
    unit_v // TRMAT_v (a, i, ord, ul, dg, lda, lu)
  , unit_v // GEMAT_v (a, i, m-i, ord, lda, lo)
  , unit_v // TRMAT_v (a, m-i, ord, ul, dg, lda, ll)
  , unit_p // (TRMAT_v (a, i, ord, ul, dg, lda, lu)
           //  GEMAT_v (a, i, m-i, ord, lda, lo)
           //  TRMAT_v (a, m-i, ord, ul, dg, lda, ll)
           // ) -<prf> TRMAT_v (a2, m, ord, ul, dg, lda, l0)
   | ptr // lu should equal l0
   , ptr // lo
   , ptr // ll
   ) = "atslib_TRMAT_ptr_split2x2_tsz"
// end of [TRMAT_ptr_split2x2_tsz]

implement
  TRMAT_ptr_split2x2_tsz_dummy (
    pf_mat | ord, ul, p_mat, lda, i, tsz
  ) = let
  prval unit_v () = pf_mat
in
  case+ ord of
  | ORDERrow () => let
      val i_tmp = size1_of_size (i * tsz) // no-op casting
      val p_tmp = p_mat + size1_of_size ((i \szmul lda) \szmul tsz)
      val p_lo = (case+ ul of
        | UPLOupper () => p_mat + i_tmp | UPLOlower () => p_tmp
      ) : ptr
    in @(
      unit_v, unit_v, unit_v, unit_p | p_mat, p_lo, p_tmp + i_tmp
    ) end // end of [ORDERrow]
  | ORDERcol () => let
      val i_tmp = size1_of_size (i * tsz) // no-op casting
      val p_tmp = p_mat + size1_of_size ((i \szmul lda) \szmul tsz)
      val p_lo = (case+ ul of
        | UPLOupper () => p_tmp | UPLOlower () => p_mat + i_tmp 
      ) : ptr
    in @(
      unit_v, unit_v, unit_v, unit_p | p_mat, p_lo, p_tmp + i_tmp
    ) end // end of [ORDERcol]
end // end of [TRMAT_ptr_split2x2_tsz_dummy]

extern fun TRMAT_ptr_split2x2_tsz
  {a1:viewt@ype} {m:nat} {i:nat | i <= m}
  {ord:order} {ul:uplo} {dg:diag} {lda:inc} {l0:addr} (
    pf_mat: TRMAT_v (a1, m, ord, ul, dg, lda, l0)
  | ord: ORDER ord, ul: UPLO ul, A: ptr l0, lda: size_t lda, i: size_t i, tsz: sizeof_t a1
  ) :<> TRMAT_ptr_split2x2_res_t (a1, m, i, ord, ul, dg, lda, l0)
// end of [TRMAT_ptr_split2x2]

implement{a1}
  TRMAT_ptr_split2x2 (pf_mat | ord, ul, A, lda, i) =
  TRMAT_ptr_split2x2_tsz (pf_mat | ord, ul, A, lda, i, sizeof<a1>)
// end of [TRMAT_ptr_split2x2]

(* ****** ****** *)

(* end of [genarrays.dats] *)
