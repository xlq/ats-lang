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

staload "libats/SATS/genmatrices.sats"

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
  GEVEC_of_GEMAT_dummy
  {a:t@ype} {ord1,ord2:order}
  {n:nat} {lda:pos} {l:addr} (
    pf: unit_v // GEMAT_v (a, 1, n, ord1, lda, l)
  | ord1: ORDER ord1, ord2: ORDER ord2, lda: int lda
  ) :<> [inc:int | inc > 0] (
    unit_v // GEVEC_v (a, n, inc, l)
  , unit_p // GEVEC_v (a, n, inc, l)
      // -<prf> GEMAT_v (a, 1, n, ord1, lda, l)
  | int inc
  ) = "atslib_GEVEC_of_GEMAT"
// end of [GEVEC_of_GEMAT_dummy]

implement
  GEVEC_of_GEMAT_dummy
  (pf | ord1, ord2, lda) = (unit_v, unit_p | inc) where {
  prval unit_v () = pf
  val inc = (case+ ord1 of
    | ORDERrow () => (case+ ord2 of ORDERrow () => 1 | _ => lda) 
    | ORDERcol () => (case+ ord2 of ORDERrow () => lda | _ => 1)
  ) : [inc:int | inc > 0] int inc
} // end of [GEVEC_of_GEMAT_dummy]

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
  ) :<> [l1,l2:addr] (
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
  ) :<> [l1,l2:addr] (
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

(* end of [genmatrices.dats] *)
