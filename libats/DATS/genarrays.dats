(*
**
** An interface for ATS to interact with BLAS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Shivkumar Chandrasekaran (shiv AT ece DOT ucsb DOT edu)
**
** Time: Summer, 2009
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

staload "libats/SATS/genarrays.sats"

(* ****** ****** *)

implement{a} GEVEC_ptr_split (pf_vec | p_vec, d, i) =
  GEVEC_ptr_split_tsz {a} (pf_vec | p_vec, d, i, sizeof<a>)
// end of [GEVEC_ptr_split]

(* ****** ****** *)

extern fun GEMAT_trans_dummy
  {a:t@ype} {ord1:order}
  {m,n:nat} {lda:pos} {l:addr} (
    pf1: unit_v // GEMAT_v (a, n, m, ord1, lda, l)
  | ord1: ORDER (ord1)
  ) :<> [ord2:order] (
    tranord_p (ord1, ord2)
  , unit_v // GEMAT_v (a, n, m, ord2, lda, l)
  | ORDER ord2
  ) = "atslib_GEMAT_trans"

implement GEMAT_trans_dummy (pf | ord1) = let
  prval unit_v () = pf
in
  case+ ord1 of
  | ORDERrow () => (TRANORDrowcol (), unit_v | ORDERcol ())
  | ORDERcol () => (TRANORDcolrow (), unit_v | ORDERrow ())
end // end of [GEMAT_trans_dummy]

(* ****** ****** *)

extern fun
  GEVEC_of_GEMAT_row_dummy
  {a:t@ype} {ord:order}
  {n:nat} {lda:pos} {l:addr} (
    pf: unit_v // GEMAT_v (a, 1, n, ord, lda, l)
  | ord: ORDER ord, lda: int lda
  ) :<> [inc:int | inc > 0] (
    unit_v // GEVEC_v (a, n, inc, l)
  , unit_p // GEVEC_v (a, n, inc, l)
      // -<prf> GEMAT_v (a, 1, n, ord, lda, l)
  | int inc
  ) = "atslib_GEVEC_of_GEMAT_row"
// end of [GEVEC_of_GEMAT_row_dummy]

implement
  GEVEC_of_GEMAT_row_dummy
  (pf | ord, lda) = let
  prval unit_v () = pf in
  case+ ord of
  | ORDERrow () => (unit_v, unit_p | 1)
  | ORDERcol () => (unit_v, unit_p | lda)
end // end of [GEVEC_of_GEMAT_row_dummy]

(* ****** ****** *)

extern fun
  GEVEC_of_GEMAT_col_dummy
  {a:t@ype} {ord:order}
  {n:nat} {lda:pos} {l:addr} (
    pf: unit_v // GEMAT_v (a, n, 1, ord, lda, l)
  | ord: ORDER ord, lda: int lda
  ) :<> [inc:int | inc > 0] (
    unit_v // GEVEC_v (a, n, inc, l)
  , unit_p // GEVEC_v (a, n, inc, l)
      // -<prf> GEMAT_v (a, n, 1, ord, lda, l)
  | int inc
  ) = "atslib_GEVEC_of_GEMAT_col"
// end of [GEVEC_of_GEMAT_col_dummy]

implement
  GEVEC_of_GEMAT_col_dummy
  (pf | ord, lda) = let
  prval unit_v () = pf in
  case+ ord of
  | ORDERrow () => (unit_v, unit_p | lda)
  | ORDERcol () => (unit_v, unit_p | 1)
end // end of [GEVEC_of_GEMAT_col_dummy]

(* ****** ****** *)

extern fun
  GEMAT_ptr_takeout_tsz_dummy
  {a:t@ype} {m,n:nat}
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

extern fun
  GEMAT_ptr_split1x2_tsz_dummy {a:t@ype} {m,n:nat}
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

extern fun GEMAT_ptr_split2x1_tsz_dummy
  {a:t@ype} {m,n:nat}
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

extern fun
  GEMAT_ptr_split2x2_tsz_dummy
  {a:t@ype}
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

implement{a} GEMAT_ptr_split1x2
  (pf_mat | p_mat, ord, lda, j) =
  GEMAT_ptr_split1x2_tsz {a} (pf_mat | p_mat, ord, lda, j, sizeof<a>)
// end of [GEMAT_ptr_split1x2]

implement{a} GEMAT_ptr_split2x1
  (pf_mat | p_mat, ord, lda, i) =
  GEMAT_ptr_split2x1_tsz {a} (pf_mat | p_mat, ord, lda, i, sizeof<a>)
// end of [GEMAT_ptr_split2x1]

implement{a} GEMAT_ptr_split2x2
  (pf_mat | p_mat, ord, lda, i, j) =
  GEMAT_ptr_split2x2_tsz {a} (pf_mat | p_mat, ord, lda, i, j, sizeof<a>)
// end of [GEMAT_ptr_split2x2]

(* ****** ****** *)

(* end of [genarrays.dats] *)
