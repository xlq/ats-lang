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

(* ****** ****** *)

%{#

#include "libats/CATS/genarrays.cats"

%}

(* ****** ****** *)

sortdef inc = {i: int | i > 0} // for incX, incY, etc.

(* ****** ****** *)

// general vector // elt, size, delta
abst@ype GEVEC (a:t@ype, n:int, d:int)

viewdef GEVEC_v
  (a:t@ype, n:int, d:int, l:addr) = GEVEC (a, n, d) @ l
// end of [GEVEC_v]

(* ****** ****** *)

fun{a:t@ype} GEVEC_ptr_split
  {n,i:nat | i <= n} {d:inc} {l0:addr} (
    pf: GEVEC_v (a, n, d, l0)
  | p_vec: ptr l0, d: int d, i: int i
  ) :<> [l:addr] (
    GEVEC_v (a, i, d, l0), GEVEC_v (a, n-i, d, l) | ptr l
  )
// end of [GEVEC_ptr_split]

fun GEVEC_ptr_split_tsz {a:t@ype}
  {n,i:nat | i <= n} {d:inc} {l0:addr} (
    pf: GEVEC_v (a, n, d, l0)
  | p_vec: ptr l0, d: int d, i: int i, tsz: sizeof_t a
  ) :<> [l:addr] (
    GEVEC_v (a, i, d, l0), GEVEC_v (a, n-i, d, l) | ptr l
  ) = "atslib_GEVEC_ptr_split_tsz"
// end of [GEVEC_ptr_split_tsz]

(* ****** ****** *)

datasort order =
  | row | col // row major / column major
// end of [order]

datatype ORDER (order) =
  | ORDERrow (row) of () | ORDERcol (col) of ()
// end of [ORDER]

(* ****** ****** *)

datasort uplo =
  | upper | lower // upper right / lower left
// end of [uplo]

datatype UPLO (uplo) =
  | UPLOupper (upper) of () | UPLOlower (lower) of ()
// end of [UPLO]

(* ****** ****** *)

datasort diag = unit | nonunit // unit / non-unit
datatype DIAG (diag) = DIAGunit (unit) | DIAGnonunit (nonunit)

(* ****** ****** *)

(*
** capturing the relation between transpose and order
*)
dataprop tranord_p (order, order) =
  | TRANORDrowcol (row, col) | TRANORDcolrow (col, row)
// end of [tranord_p]

(* ****** ****** *)

//
// GEneral MATrix representation
//

// elt, row, col, ord, lda
abst@ype GEMAT
  (a:t@ype, m:int, n:int, ord:order, lda:int)
// end of [GEMAT]

viewdef GEMAT_v
  (a:t@ype, m:int, n:int, ord: order, lda:int, l:addr) =
  GEMAT (a, m, n, ord, lda) @ l
// end of [GEMAT_v]

(* ****** ****** *)

prfun GEMAT_trans
  {a:t@ype} {ord1:order}
  {m,n:nat} {lda:pos} {l:addr} (
    pf_mat: !GEMAT_v (a, m, n, ord1, lda, l) >>
             GEMAT_v (a, n, m, ord2, lda, l)
    // end of [pf_mat]
  ) :<> #[ord2:order] tranord_p (ord1, ord2)
// end of [GEMAT_trans]

(* ****** ****** *)

// implemented in [genarrays.dats]
fun GEVEC_of_GEMAT_row // as GEVEC_of_GEMAT_row_dummy
  {a:t@ype} {ord:order}
  {n:nat} {lda:pos} {l:addr} (
    pf: GEMAT_v (a, 1, n, ord, lda, l)
  | ord1: ORDER ord, lda: int lda
  ) :<> [inc:int | inc > 0] (
    GEVEC_v (a, n, inc, l)
  , GEVEC_v (a, n, inc, l) -<prf> GEMAT_v (a, 1, n, ord, lda, l)
  | int inc
  ) = "atslib_GEVEC_of_GEMAT_row"
// end of [GEVEC_of_GEMAT_row]

// implemented in [genarrays.dats]
fun GEVEC_of_GEMAT_col // as GEVEC_of_GEMAT_col_dummy
  {a:t@ype} {ord:order}
  {n:nat} {lda:pos} {l:addr} (
    pf: GEMAT_v (a, n, 1, ord, lda, l)
  | ord1: ORDER ord, lda: int lda
  ) :<> [inc:int | inc > 0] (
    GEVEC_v (a, n, inc, l)
  , GEVEC_v (a, n, inc, l) -<prf> GEMAT_v (a, n, 1, ord, lda, l)
  | int inc
  ) = "atslib_GEVEC_of_GEMAT_col"
// end of [GEVEC_of_GEMAT_col]

(* ****** ****** *)

fun{a:t@ype} GEMAT_ptr_takeout {m,n:nat}
  {i,j:nat | i < m; j < n} {ord:order} {lda:pos} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , i: int i, j: int j
  ) :<> [l:addr] (
    a @ l
  , a @ l -<lin,prf> GEMAT_v (a, m, n, ord, lda, l0)
  | ptr l
  )
// end of [GEMAT_ptr_takeout]

fun GEMAT_ptr_takeout_tsz {a:t@ype} {m,n:nat}
  {i,j:nat | i < m; j < n} {ord:order} {lda:pos} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , i: int i, j: int j
  , tsz: sizeof_t a
  ) :<> [l:addr] (
    a @ l
  , a @ l -<lin,prf> GEMAT_v (a, m, n, ord, lda, l0)
  | ptr l
  ) = "atslib_GEMAT_ptr_takeout_tsz"
// end of [GEMAT_ptr_takeout_tsz]

(* ****** ****** *)

fun{a:t@ype} GEMAT_ptr_get_elt_at {m,n:nat}
  {i,j:nat | i < m; j < n} {ord:order} {lda:pos} (
    A: &GEMAT (a, m, n, ord, lda)
  , ord: ORDER ord
  , lda: int lda
  , i: int i, j: int j
  ) :<> a
// end of [GEMAT_ptr_get_elt_at]

fun{a:t@ype} GEMAT_ptr_set_elt_at {m,n:nat}
  {i,j:nat | i < m; j < n} {ord:order} {lda:pos} (
    A: &GEMAT (a, m, n, ord, lda)
  , ord: ORDER ord
  , lda: int lda
  , i: int i, j: int j
  , x: a
  ) :<> void 
// end of [GEMAT_ptr_set_elt_at]

(* ****** ****** *)

viewtypedef GEMAT_ptr_split1x2_res_t (
  a:t@ype, m:int, n:int, j:int, ord:order, lda:int, l0:addr
) = [l1,l2:addr] @(
  GEMAT_v (a, m, j, ord, lda, l1)  
, GEMAT_v (a, m, n-j, ord, lda, l2)
, (GEMAT_v (a, m, j, ord, lda, l1),
   GEMAT_v (a, m, n-j, ord, lda, l2)
  ) -<prf>
    GEMAT_v (a, m, n, ord, lda, l0)
  // [fpf]
| ptr l1 // l1 should equal l0
, ptr l2
) // end of [GEMAT_ptr_split1x2_res_t]

fun{a:t@ype} GEMAT_ptr_split1x2 {m,n:nat}
  {j:nat | j <= n} {ord:order} {lda:pos} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , j: int j
  ) :<> GEMAT_ptr_split1x2_res_t (a, m, n, j, ord, lda, l0)
// end of [GEMAT_ptr_split1x2]

fun GEMAT_ptr_split1x2_tsz {a:t@ype} {m,n:nat}
  {j:nat | j <= n} {ord:order} {lda:pos} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , j: int j
  , tsz: sizeof_t a
  ) :<> GEMAT_ptr_split1x2_res_t (a, m, n, j, ord, lda, l0)
    = "atslib_GEMAT_ptr_split1x2_tsz"
(* end of [GEMAT_ptr_split1x2_tsz] *)

(* ****** ****** *)

viewtypedef GEMAT_ptr_split2x1_res_t (
  a:t@ype, m:int, n:int, i:int, ord:order, lda:int, l0:addr
) = [l1,l2:addr] @(
  GEMAT_v (a, i, n, ord, lda, l1)  
, GEMAT_v (a, m-i, n, ord, lda, l2)
, (GEMAT_v (a, i, n, ord, lda, l1),
   GEMAT_v (a, m-i, n, ord, lda, l2)
  ) -<prf>
    GEMAT_v (a, m, n, ord, lda, l0)
  // [fpf]
| ptr l1 // l1 should equal l0
, ptr l2
) // end of [GEMAT_ptr_split2x1_res_t]

fun{a:t@ype} GEMAT_ptr_split2x1 {m,n:nat}
  {i,j:nat | i <= m} {ord:order} {lda:pos} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , i: int i
  ) :<> GEMAT_ptr_split2x1_res_t (a, m, n, i, ord, lda, l0)
// end of [GEMAT_ptr_split2x1]

fun GEMAT_ptr_split2x1_tsz {a:t@ype} {m,n:nat}
  {i:nat | i <= m} {ord:order} {lda:pos} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , i: int i
  , tsz: sizeof_t a
  ) :<> GEMAT_ptr_split2x1_res_t (a, m, n, i, ord, lda, l0)
    = "atslib_GEMAT_ptr_split2x1_tsz"
(* end of [GEMAT_ptr_split2x1_tsz] *)

(* ****** ****** *)

viewtypedef GEMAT_ptr_split2x2_res_t (
  a:t@ype, m:int, n:int, i:int, j:int, ord:order, lda:int, l0:addr
) = [l11,l12,l21,l22:addr] @(
  GEMAT_v (a, i, j, ord, lda, l11)  
, GEMAT_v (a, i, n-j, ord, lda, l12)
, GEMAT_v (a, m-i, j, ord, lda, l21)
, GEMAT_v (a, m-i, n-j, ord, lda, l22)
, (GEMAT_v (a, i, j, ord, lda, l11),
   GEMAT_v (a, i, n-j, ord, lda, l12),
   GEMAT_v (a, m-i, j, ord, lda, l21),
   GEMAT_v (a, m-i, n-j, ord, lda, l22)
  ) -<prf>
    GEMAT_v (a, m, n, ord, lda, l0)
  // [fpf]
| ptr l11 // l11 should equal l0
, ptr l12
, ptr l21
, ptr l22
) // end of [GEMAT_ptr_split2x2_res_t]

fun{a:t@ype} GEMAT_ptr_split2x2
  {m,n:nat}
  {i,j:nat | i <= m; j <= n}
  {ord:order} {lda:pos} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , i: int i, j: int j
  ) :<> GEMAT_ptr_split2x2_res_t (a, m, n, i, j, ord, lda, l0)
// end of [GEMAT_ptr_split2x2]

fun GEMAT_ptr_split2x2_tsz
  {a:t@ype} {m,n:nat}
  {i,j:nat | i <= m; j <= n}
  {ord:order} {lda:pos} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | p_mat: ptr l0
  , ord: ORDER ord
  , lda: int lda
  , i: int i, j: int j
  , tsz: sizeof_t a
  ) :<> GEMAT_ptr_split2x2_res_t (a, m, n, i, j, ord, lda, l0)
  = "atslib_GEMAT_ptr_split2x2_tsz"
// end of [GEMAT_ptr_split2x2_tsz]

(* ****** ****** *)

(* end of [genarrays.sats] *)


