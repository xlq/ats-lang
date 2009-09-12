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

staload "libats/SATS/genarrays.sats"

(* ****** ****** *)

implement{a} GEVEC_ptr_takeout (pf_vec | p_vec, d, i) =
  GEVEC_ptr_takeout_tsz {a} (pf_vec | p_vec, d, i, sizeof<a>)
// end of [GEVEC_ptr_takeout]

(* ****** ****** *)

implement{a1} GEVEC_ptr_split (pf_vec | p_vec, d, i) =
  GEVEC_ptr_split_tsz {a1} (pf_vec | p_vec, d, i, sizeof<a1>)
// end of [GEVEC_ptr_split]

(* ****** ****** *)

implement{a} GEVEC_ptr_get_elt_at (V, d, i) = x where {
  val (pf, fpf | p) =
    GEVEC_ptr_takeout_tsz {a} (view@ V | &V, d, i, sizeof<a>)
  // end of [val]  
  val x = !p
  prval () = view@ V := fpf (pf)
} // end of [GEVEC_ptr_get_elt_at]

implement{a} GEVEC_ptr_set_elt_at (V, d, i, x) = () where {
  val (pf, fpf | p) =
    GEVEC_ptr_takeout_tsz {a} (view@ V | &V, d, i, sizeof<a>)
  // end of [val]  
  val () = !p := x
  prval () = view@ V := fpf (pf)
} // end of [GEVEC_ptr_set_elt_at]

(* ****** ****** *)

implement
  GEVEC_ptr_foreach_fun_tsz__main
    {a} {v} {vt} {n} {d}
    (pf | base, f, vsz, inc, tsz, env) = let
  fun loop {l:addr} {n:nat} .<n>. (
      pf: !v
    , pf_vec: !GEVEC_v (a, n, d, l)
    | p: ptr l, n: int n, env: !vt
    ) :<cloref> void =
    if n > 0 then let
      prval (pf_at, fpf_vec) = GEVEC_v_uncons (pf_vec)
      val () = f (pf | !p, env)
      prval () = pf_vec := fpf_vec (pf_at)
      val (pf1_vec, pf2_vec, fpf_vec | p1) =
        GEVEC_ptr_split_tsz (pf_vec | p, inc, 1, tsz)
      val () = loop (pf, pf2_vec | p1, n-1, env)
      prval () = pf_vec := fpf_vec (pf1_vec, pf2_vec)
    in
      // nothing
    end // end of [if]
  (* end of [loop] *)
in
  loop (pf, view@ base | &base, vsz, env)
end // end of [GEVEC_ptr_foreach_fun_tsz__main]

//

implement GEVEC_ptr_foreach_fun_tsz
  {a} {v} (pf | base, f, n, inc, tsz) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (!v | &a) -<> void) :<> (!v | &a, !ptr) -<> void
  } // end of [where]
in
  GEVEC_ptr_foreach_fun_tsz__main (pf | base, f, n, inc, tsz, null)
end // end of [GEVEC_ptr_foreach_fun_tsz]

//

implement GEVEC_ptr_foreach_clo_tsz
  {a} {v} (pf_v | base, f, vsz, inc, tsz) = let
  stavar l_f: addr
  val p_f: ptr l_f = &f
  typedef clo_t = (!v | &a) -<clo> void
  viewdef V = @(v, clo_t @ l_f)
  fn app (pf: !V | x: &a, p_f: !ptr l_f):<> void = let
    prval (pf1, pf2) = pf in !p_f (pf1 | x); pf := @(pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = GEVEC_ptr_foreach_fun_tsz__main
    {a} {V} {ptr l_f} (pf | base, app, vsz, inc, tsz, p_f)
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
  fun loop {l:addr}
    {ni:nat | ni <= n} .<ni>. (
      pf: !v
    , pf_vec: !GEVEC_v (a, ni, d, l)
    | p: ptr l, ni: int ni, env: !vt
    ) :<cloref> void =
    if ni > 0 then let
      prval (pf_at, fpf_vec) = GEVEC_v_uncons (pf_vec)
      val () = f (pf | vsz - ni, !p, env)
      prval () = pf_vec := fpf_vec (pf_at)
      val (pf1_vec, pf2_vec, fpf_vec | p1) =
        GEVEC_ptr_split_tsz (pf_vec | p, inc, 1, tsz)
      val () = loop (pf, pf2_vec | p1, ni-1, env)
      prval () = pf_vec := fpf_vec (pf1_vec, pf2_vec)
    in
      // nothing
    end // end of [if]
  (* end of [loop] *)
in
  loop (pf, view@ base | &base, vsz, env)
end // end of [GEVEC_ptr_iforeach_fun_tsz__main]

//

implement GEVEC_ptr_iforeach_fun_tsz
  {a} {v} {n} (pf | base, f, n, inc, tsz) = let
  val f = coerce (f) where {
    extern castfn coerce
      (f: (!v | natLt n, &a) -<> void)
      :<> (!v | natLt n, &a, !ptr) -<> void
  } // end of [where]
in
  GEVEC_ptr_iforeach_fun_tsz__main (pf | base, f, n, inc, tsz, null)
end // end of [GEVEC_ptr_iforeach_fun_tsz]

(* ****** ****** *)

implement
  GEVEC_ptr_iforeach_clo_tsz__main
    {a} {v} {vt} {n} {d}
    (pf | base, f, vsz, inc, tsz, env) = let
  fun loop {l:addr}
    {ni:nat | ni <= n} .<ni>. (
      pf: !v
    , pf_vec: !GEVEC_v (a, ni, d, l)
    | p: ptr l
    , f: &(!v | natLt n, &a, !vt) -<clo> void
    , ni: int ni, env: !vt
    ) :<cloref> void =
    if ni > 0 then let
      prval (pf_at, fpf_vec) = GEVEC_v_uncons (pf_vec)
      val () = f (pf | vsz - ni, !p, env)
      prval () = pf_vec := fpf_vec (pf_at)
      val (pf1_vec, pf2_vec, fpf_vec | p1) =
        GEVEC_ptr_split_tsz (pf_vec | p, inc, 1, tsz)
      val () = loop (pf, pf2_vec | p1, f, ni-1, env)
      prval () = pf_vec := fpf_vec (pf1_vec, pf2_vec)
    in
      // nothing
    end // end of [if]
  (* end of [loop] *)
in
  loop (pf, view@ base | &base, f, vsz, env)
end // end of [GEVEC_ptr_iforeach_clo_tsz__main]

//

implement GEVEC_ptr_iforeach_clo_tsz
  {a} {v} {n} (pf | base, f, n, inc, tsz) = let
  stavar l_f: addr
  val p_f = (&f: ptr l_f)
  typedef clo_t = (!v | natLt n, &a) -<clo> void
  typedef clo1_t = (!v | natLt n, &a, !ptr) -<clo> void
  prval () = view@ f := coerce (view@ f) where {
    extern prfun coerce (pf_clo: clo_t @ l_f): clo1_t @ l_f
  } // end of [where]
  val () = GEVEC_ptr_iforeach_clo_tsz__main {a} {v} {ptr} (pf | base, f, n, inc, tsz, null)
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

(*
** The following function acts as a dummy for [GEMAT_ptr_takeout_tsz]
*)
extern fun
  GEMAT_ptr_takeout_tsz_dummy
  {a:viewt@ype} {m,n:nat}
  {i,j:nat | i < m; j < n}
  {ord:order} {lda:pos} {l0:addr} (
    pf_mat: unit_v // GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , i: int i, j: int j
  , tsz: sizeof_t a
  ) :<> [l:addr] (
    unit_v // a @ l
  , unit_v // a @ l -<lin,prf> GEMAT_v (a, m, n, ord, lda, l0)
  | ptr l
  ) = "atslib_GEMAT_ptr_takeout_tsz"
// end of [GEMAT_ptr_takeout_tsz_dummy]

implement GEMAT_ptr_takeout_tsz_dummy
  (pf_mat | p_mat, ord, lda, i, j, tsz) = let
  prval unit_v () = pf_mat
  val i = size_of_int1 i
  val lda = size_of_int1 lda
  val j = size_of_int1 j
  val ofs = (case+ ord of
    | ORDERrow () => (i * lda) + j
    | ORDERcol () => i + (j * lda)
  ) : size_t
  val ofs = size1_of_size (ofs)
in
  (unit_v, unit_v | p_mat + ofs * tsz)
end // end of [GEMAT_ptr_takeout_tsz_dummy]

(* ****** ****** *)

implement{a} GEMAT_ptr_takeout (pf_mat | p, ord, lda, i, j) =
  GEMAT_ptr_takeout_tsz {a} (pf_mat | p, ord, lda, i, j, sizeof<a>)
// end of [GEMAT_takeout]

implement{a} GEMAT_ptr_get_elt_at (A, ord, lda, i, j) = let
  val (pf, fpf | p) =
    GEMAT_ptr_takeout_tsz {a} (view@ A | &A, ord, lda, i, j, sizeof<a>)
  // end of [val]  
  val x = !p
  prval () = view@ A := fpf (pf)
in
  x // the return value
end // end of [GEMAT_ptr_get_elt_at]

implement{a} GEMAT_ptr_set_elt_at (A, ord, lda, i, j, x) = let
  val (pf, fpf | p) =
    GEMAT_ptr_takeout_tsz {a} (view@ A | &A, ord, lda, i, j, sizeof<a>)
  // end of [val]  
  val () = !p := x
  prval () = view@ A := fpf (pf)
in
  // nothing
end // end of [GEMAT_ptr_set_elt_at]

(* ****** ****** *)

(*
** The following function acts as a dummy for [GEMAT_ptr_tail_row_tsz]
*)
extern fun GEMAT_ptr_tail_row_tsz_dummy
  {a:viewt@ype} {m:pos;n:nat}
  {ord:order} {lda:pos} {l0:addr} (
    pf_mat: unit_v // GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , tsz: sizeof_t a
  ) :<> [l:addr] (
    unit_v // GEMAT_v (a, m-1, n, ord, lda, l)
  , unit_v // GEMAT_v (a, m-1, n, ord, lda, l) -<lin,prf> GEMAT_v (a, m, n, ord, lda, l0)
  | ptr l
  ) = "atslib_GEMAT_ptr_tail_row_tsz"
// end of [GEMAT_ptr_tail_row_tsz]

implement GEMAT_ptr_tail_row_tsz_dummy
  (pf_mat | p_mat, ord, lda, tsz) = let
  prval unit_v () = pf_mat
  val ofs = (case+ ord of
    | ORDERrow () => size1_of_int1 lda * tsz | ORDERcol () => tsz
  ) : size_t // end of [val]
  val ofs = size1_of_size (ofs)
in
  (unit_v (), unit_v () | p_mat + ofs)
end // end of [GEMAT_ptr_tail_row_tsz_dummy]

implement{a} GEMAT_ptr_tail_row (pf_mat | p_mat, ord, lda) =
  GEMAT_ptr_tail_row_tsz (pf_mat | p_mat, ord, lda, sizeof<a>)
// end of [GEMAT_ptr_tail_row]

(* ****** ****** *)

(*
** The following function acts as a dummy for [GEMAT_ptr_tail_col_tsz]
*)
extern fun GEMAT_ptr_tail_col_tsz_dummy
  {a:viewt@ype} {m:pos;n:nat}
  {ord:order} {lda:pos} {l0:addr} (
    pf_mat: unit_v // GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , tsz: sizeof_t a
  ) :<> [l:addr] (
    unit_v // GEMAT_v (a, m-1, n, ord, lda, l)
  , unit_v // GEMAT_v (a, m-1, n, ord, lda, l) -<lin,prf> GEMAT_v (a, m, n, ord, lda, l0)
  | ptr l
  ) = "atslib_GEMAT_ptr_tail_col_tsz"
// end of [GEMAT_ptr_tail_col_tsz]

implement GEMAT_ptr_tail_col_tsz_dummy
  (pf_mat | p_mat, ord, lda, tsz) = let
  prval unit_v () = pf_mat
  val ofs = (case+ ord of
    | ORDERrow () => tsz | ORDERcol () => size1_of_int1 lda * tsz
  ) : size_t // end of [val]
  val ofs = size1_of_size (ofs)
in
  (unit_v (), unit_v () | p_mat + ofs)
end // end of [GEMAT_ptr_tail_col_tsz_dummy]

implement{a} GEMAT_ptr_tail_col (pf_mat | p_mat, ord, lda) =
  GEMAT_ptr_tail_col_tsz (pf_mat | p_mat, ord, lda, sizeof<a>)
// end of [GEMAT_ptr_tail_col]

(* ****** ****** *)

(*
** The following function acts as a dummy for [GEMAT_ptr_split1x2_tsz]
*)
extern fun
GEMAT_ptr_split1x2_tsz_dummy
  {a:viewt@ype} {m,n:nat}
  {j:nat | j <= n} {ord:order} {lda:pos} {l0:addr} (
    pf_mat: unit_v // GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , j: int j
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
  (pf_mat | p_mat, ord, lda, j, tsz) = let
  prval unit_v () = pf_mat
  val j = size1_of_int1 (j)
  val ofs = (case ord of
    | ORDERrow () => j | ORDERcol () => j * size1_of_int1 (lda)
  ) : size_t // end of [val]
  val ofs = size1_of_size (ofs)
in
  (unit_v, unit_v, unit_p | p_mat, p_mat + ofs * tsz)
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
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , i: int i
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
  (pf_mat | p_mat, ord, lda, i, tsz) = let
  prval unit_v () = pf_mat
  val i = size1_of_int1 (i)
  val ofs = (case ord of
    | ORDERrow () => i  * size1_of_int1 (lda) | ORDERcol () => i
  ) : size_t // end of [val]
  val ofs = size1_of_size (ofs)
in
  (unit_v, unit_v, unit_p | p_mat, p_mat + ofs * tsz)
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
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , i: int i, j: int j
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
    pf_mat | p_mat , ord, lda, i, j, tsz
  ) = let
  prval unit_v () = pf_mat
  val i = size_of_int1 i and j = size_of_int1 j
  val lda = size_of_int1 lda
in
  case+ ord of
  | ORDERrow () => let
      val i_tmp = size1_of_size (j * tsz)
      val p_tmp = p_mat + size1_of_size ((i * lda) * tsz)
    in @(
      unit_v, unit_v, unit_v, unit_v, unit_p
    | p_mat, p_mat + i_tmp, p_tmp, p_tmp + i_tmp
    ) end // end of [ORDERrow]
  | ORDERcol () => let
      val i_tmp = size1_of_size (i * tsz)
      val p_tmp = p_mat + size1_of_size ((j * lda) * tsz)
    in @(
      unit_v, unit_v, unit_v, unit_v, unit_p
    | p_mat, p_tmp, p_mat + i_tmp, p_tmp + i_tmp
    ) end // end of [ORDERcol]
end // end of [GEMAT_ptr_split2x2_tsz_dummy]

(* ****** ****** *)

implement{a1} GEMAT_ptr_split1x2
  (pf_mat | p_mat, ord, lda, j) =
  GEMAT_ptr_split1x2_tsz {a1} (pf_mat | p_mat, ord, lda, j, sizeof<a1>)
// end of [GEMAT_ptr_split1x2]

implement{a1} GEMAT_ptr_split2x1
  (pf_mat | p_mat, ord, lda, i) =
  GEMAT_ptr_split2x1_tsz {a1} (pf_mat | p_mat, ord, lda, i, sizeof<a1>)
// end of [GEMAT_ptr_split2x1]

implement{a1} GEMAT_ptr_split2x2
  (pf_mat | p_mat, ord, lda, i, j) =
  GEMAT_ptr_split2x2_tsz {a1} (pf_mat | p_mat, ord, lda, i, j, sizeof<a1>)
// end of [GEMAT_ptr_split2x2]

(* ****** ****** *)

implement
GEMAT_ptr_foreach_fun_tsz__main
  {a} {v} {vt} {ord1,ord2} {m,n} {ld}
  (pf | M, f, ord1, ord2, m, n, ld, tsz, env) = let
  fun loop_row {n > 0}
    {mi:nat | mi <= m} {l:addr} .<mi>. (
    pf: !v
  , pf_mat: !GEMAT_v (a, mi, n, ord1, ld, l)
  | p: ptr l
  , mi: int mi
  , env: !vt
  ) :<cloref> void =
  if mi > 0 then let
    val (pf1_mat, pf2_mat, fpf | p1, p2) =
      GEMAT_ptr_split2x1_tsz {a} (pf_mat | p, ord1, ld, 1, tsz)
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
  , ni: int ni
  , env: !vt
  ) :<cloref> void =
  if ni > 0 then let
    val (pf1_mat, pf2_mat, fpf | p1, p2) =
      GEMAT_ptr_split1x2_tsz {a} (pf_mat | p, ord1, ld, 1, tsz)
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

implement GEMAT_ptr_foreach_fun_tsz
  {a} {v} {ord1,ord2} {m,n}
  (pf | base, f, ord1, ord2, m, n, ld, tsz) = let
  val f = coerce (f) where {
    extern castfn coerce
      (f: (!v | &a) -<> void):<> (!v | &a, !ptr) -<> void
  } // end of [where]
in
  GEMAT_ptr_foreach_fun_tsz__main
    (pf | base, f, ord1, ord2, m, n, ld, tsz, null)
end // end of [GEMAT_ptr_foreach_fun_tsz]

implement GEMAT_ptr_foreach_clo_tsz
  {a} {v} {ord1,ord2} {m,n}
  (pf_v | M, f, ord1, ord2, m, n, ld, tsz) = let
  viewtypedef clo_t = (!v | &a) -<clo> void
  stavar l_f: addr
  val p_f: ptr l_f = &f
  viewdef V = @(v, clo_t @ l_f)
  fn app (pf: !V | x: &a, p_f: !ptr l_f):<> void = let
    prval (pf1, pf2) = pf; val () = !p_f (pf1 | x) in pf := (pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = GEMAT_ptr_foreach_fun_tsz__main
    {a} {V} {ptr l_f} (pf | M, app, ord1, ord2, m, n, ld, tsz, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [GEMAT_ptr_foreach_clo_tsz]

(* ****** ****** *)

implement
GEMAT_ptr_iforeach_fun_tsz__main
  {a} {v} {vt} {ord1,ord2} {m,n} {ld}
  (pf | M, f, ord1, ord2, m, n, ld, tsz, env) = let
  fun loop_row {n > 0}
    {mi:nat | mi <= m} {l:addr} .<mi>. (
    pf: !v
  , pf_mat: !GEMAT_v (a, mi, n, ord1, ld, l)
  | p: ptr l
  , mi: int mi
  , env: !vt
  ) :<cloref> void =
  if mi > 0 then let
    val (pf1_mat, pf2_mat, fpf | p1, p2) =
      GEMAT_ptr_split2x1_tsz {a} (pf_mat | p, ord1, ld, 1, tsz)
    prval (pf1_inc, pf1_vec, fpf1_mat) =
      GEVEC_v_of_GEMAT_v_row (pf1_mat, ord1, ld)
    val inc = MATVECINC_get (pf1_inc | ORDERrow, ord1, ld)
    val () = GEVEC_ptr_iforeach_clo_tsz__main
      {a} {v} (pf | !p1, !p_clo, n, inc, tsz, env) where {
      val i = m - mi
      var !p_clo = @lam
        (pf: !v | j: natLt n, x: &a, env: !vt): void =<clo> f (pf | i, j, x, env)
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
  , nj: int nj
  , env: !vt
  ) :<cloref> void =
  if nj > 0 then let
    val (pf1_mat, pf2_mat, fpf | p1, p2) =
      GEMAT_ptr_split1x2_tsz {a} (pf_mat | p, ord1, ld, 1, tsz)
    prval (pf1_inc, pf1_vec, fpf1_mat) =
      GEVEC_v_of_GEMAT_v_col (pf1_mat, ord1, ld)
    val inc = MATVECINC_get (pf1_inc | ORDERcol, ord1, ld)
    val () = GEVEC_ptr_iforeach_clo_tsz__main
      {a} {v} (pf | !p1, !p_clo, m, inc, tsz, env) where {
      val j = n-nj
      var !p_clo = @lam
        (pf: !v | i: natLt m, x: &a, env: !vt): void =<clo> f (pf | i, j, x, env)
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

implement GEMAT_ptr_iforeach_fun_tsz
  {a} {v} {ord1,ord2} {m,n}
  (pf | base, f, ord1, ord2, m, n, ld, tsz) = let
  val f = coerce (f) where {
    extern castfn coerce
      (f: (!v | natLt m, natLt n, &a) -<> void)
      :<> (!v | natLt m, natLt n, &a, !ptr) -<> void
  } // end of [where]
in
  GEMAT_ptr_iforeach_fun_tsz__main
    (pf | base, f, ord1, ord2, m, n, ld, tsz, null)
end // end of [GEMAT_ptr_iforeach_fun_tsz]

(* ****** ****** *)

implement GEMAT_ptr_iforeach_clo_tsz
  {a} {v} {ord1,ord2} {m,n}
  (pf_v | M, f, ord1, ord2, m, n, ld, tsz) = let
  viewtypedef clo_t = (!v | natLt m, natLt n, &a) -<clo> void
  stavar l_f: addr
  val p_f: ptr l_f = &f
  viewdef V = @(v, clo_t @ l_f)
  fn app (
      pf: !V
    | i: natLt m, j: natLt n, x: &a, p_f: !ptr l_f
    ) :<> void = let
    prval (pf1, pf2) = pf; val () = !p_f (pf1 | i, j, x) in pf := (pf1, pf2)
  end // end of [app]
  prval pf = (pf_v, view@ f)
  val () = GEMAT_ptr_iforeach_fun_tsz__main
    {a} {V} {ptr l_f} (pf | M, app, ord1, ord2, m, n, ld, tsz, p_f)
  prval (pf1, pf2) = pf
  prval () = (pf_v := pf1; view@ f := pf2)
in
  // empty
end // end of [GEMAT_ptr_iforeach_clo_tsz]

(* ****** ****** *)

(* end of [genarrays.dats] *)
