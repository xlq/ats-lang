(*
**
** An interface for ATS to interact with BLAS and LAPACK
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Shivkumar Chandrasekaran (shiv AT ece DOT ucsb DOT edu)
**
** Time: Summer, 2009
**
*)

(* ****** ****** *)

//
// Fortran matrices: column-major representation
//

(* ****** ****** *)

%{#

#include "libats/CATS/fmatrix.cats"

%}

(* ****** ****** *)

staload "libats/SATS/genarrays.sats"

(* ****** ****** *)

abst@ype fmatrix_t0ype_int_int_t0ype (a: t@ype, row: int, col: int)

stadef fmatrix = fmatrix_t0ype_int_int_t0ype
viewdef fmatrix_v
  (a: t@ype, row: int, col: int, l:addr) = fmatrix (a, row, col) @ l
// end of [fmatrix_v]

(* ****** ****** *)

prfun array_v_of_fmatrix_v {a:t@ype} {m,n:int} {l:addr}
  (pf_mat: fmatrix_v (a, m, n, l)):<> [mn:int] (MUL (m, n, mn), array_v (a, mn, l))

prfun fmatrix_v_of_array_v {a:t@ype} {m,n:int} {mn:int} {l:addr}
  (pf_mul: MUL (m, n, mn), pf_arr: array_v (a, mn, l)):<> fmatrix_v (a, m, n, l)

(* ****** ****** *)

fun fmatrix_ptr_initialize_elt_tsz {a:t@ype}
  {m,n:nat} {l:addr} (
    base:
      &fmatrix (a?, m, n) >> fmatrix (a, m, n)
    // end of [base]
  , m: int m, n: int n, x: &a, tsz: sizeof_t a
  ) :<> void
// end of [fmatrix_initialize_elt_tsz]

(* ****** ****** *)

fun fmatrix_ptr_initialize_clo_tsz
  {a:t@ype} {v:view} {m,n:nat} (
    pf: !v 
  | base: &fmatrix (a?, m, n) >> fmatrix (a, m, n)
  , m: int m, n: int n
  , f: &(!v | &(a?) >> a, natLt m, natLt n) -<clo> void
  , tsz: sizeof_t a
  ) :<> void
// end of [fmatrix_ptr_initialize_clo_tsz]

(* ****** ****** *)

fun{a:t@ype} fmatrix_ptr_takeout
  {m,n:int} {i,j:nat | i < m; j < n} {l0:addr} (
    pf_mat: fmatrix_v (a, m, n, l0)
  | base: ptr l0, i: int i, m: int m, j: int j
  ) :<> [l:addr] (
    a @ l
  , a @ l -<lin,prf> fmatrix_v (a, m, n, l0)
  | ptr l
  ) // end of [fmatrix_ptr_takeout]
(* end of [fmatrix_ptr_takeout] *)

fun fmatrix_ptr_takeout_tsz {a:t@ype}
  {m,n:int} {i,j:nat | i < m; j < n} {l0:addr} (
    pf_mat: fmatrix_v (a, m, n, l0)
  | base: ptr l0, i: int i, m: int m, j: int j, tsz: sizeof_t a
  ) :<> [l:addr] (
    a @ l
  , a @ l -<lin,prf> fmatrix_v (a, m, n, l0)
  | ptr l
  ) // end of [fmatrix_ptr_takeout_tsz]
    = "atslib_fmatrix_ptr_takeout_tsz"
(* end of [fmatrix_ptr_takeout_tsz] *)

(* ****** ****** *)

fun{a:t@ype} fmatrix_ptr_get_elt_at
  {m,n:int} {i,j:nat | i < m; j < n} (
    base: &fmatrix (a, m, n), i: int i, m: int m, j: int j
  ) :<> a
(* end of [fmatrix_ptr_ptr_get_elt_at] *)

fun{a:t@ype} fmatrix_ptr_set_elt_at
  {m,n:int} {i,j:nat | i < m; j < n} (
    base: &fmatrix (a, m, n), i: int i, m: int m, j: int j, x: a
  ) :<> void
(* end of [fmatrix_ptr_ptr_set_elt_at] *)

overload [] with fmatrix_ptr_get_elt_at
overload [] with fmatrix_ptr_set_elt_at

(* ****** ****** *)

prfun GEVEC_of_fmatrix
  {a:t@ype} {m,n:nat} {mn:nat} {l:addr} (
    pf_mul: MUL (m, n, mn), pf_mat: fmatrix_v (a, m, n, l)
  ) :<> (
    GEVEC_v (a, mn, 1, l)
  , GEVEC_v (a, mn, 1, l) -<prf> fmatrix_v (a, m, n, l)
  )
// end of [GEVEC_of_fmatrix]

(* ****** ****** *)

prfun GEMAT_of_fmatrix
  {a:t@ype} {m,n:nat} {l:addr} (
    pf_mat: fmatrix_v (a, m, n, l)
  ) :<> (
    GEMAT_v (a, m, n, col, m, l)
  , GEMAT_v (a, m, n, col, m, l) -> fmatrix_v (a, m, n, l)
  )
// end of [GEMAT_of_fmatrix]

(* ****** ****** *)

(*

fun GEMAT_trans
  {a:t@ype}
  {ord1:order}
  {m,n:nat} {lda:pos} {l:addr} (
    pf1: GEMAT_v (a, m, n, ord1, lda, l)
  | ord1: CBLAS_ORDER_t (ord1)
  ) :<> [ord2:order] (
    tranord_p (ord1, ord2)
  , GEMAT_v (a, n, m, ord2, lda, l) | CBLAS_ORDER_t (ord2)
  ) // end of [GEMAT_trans]
  = "atslib_GEMAT_trans"

*)

(* ****** ****** *)

fun GEVEC_of_GEMAT_row
  {a:t@ype} {ord:order} {n:nat} {lda:pos} {l:addr} (
    pf: GEMAT_v (a, 1, n, ord, lda, l) | ord: ORDER ord, lda: int lda
  ) :<> [inc:int | inc > 0] (
    GEVEC_v (a, n, inc, l)
  , GEVEC_v (a, n, inc, l) -<prf> GEMAT_v (a, 1, n, ord, lda, l)
  | int inc
  ) = "atslib_GEVEC_of_GEMAT_row"
// end of [GEVEC_of_GEMAT_row]

fun GEVEC_of_GEMAT_col
  {a:t@ype} {ord:order} {m:nat} {lda:pos} {l:addr} (
    pf: GEMAT_v (a, m, 1, ord, lda, l) | ord: ORDER ord, lda: int lda
  ) :<> [inc:int | inc > 0] (
    GEVEC_v (a, m, inc, l)
  , GEVEC_v (a, m, inc, l) -<prf> GEMAT_v (a, m, 1, ord, lda, l)
  | int inc
  ) = "atslib_GEVEC_of_GEMAT_col"
// end of [GEVEC_of_GEMAT_col]

(* ****** ****** *)

(* end of [fmatrix.sats] *)
