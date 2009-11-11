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

%{#

#include "libats/CATS/genarrays.cats"

%}

(* ****** ****** *)

sortdef inc = {i: int | i > 0} // for incX, incY, etc.

(* ****** ****** *)

// general vector // elt, size, delta
absviewt@ype GEVEC (a:viewt@ype+, n:int, d:int)

viewdef GEVEC_v
  (a:viewt@ype, n:int, d:int, l:addr) = GEVEC (a, n, d) @ l
// end of [GEVEC_v]

(* ****** ****** *)

prfun GEVEC_v_nil
  {a:viewt@ype} {d:inc} {l:addr} ():<prf> GEVEC_v (a, 0, d, l)
// end of [GEVEC_v_nil]

prfun GEVEC_v_unnil
  {a:viewt@ype} {d:inc} {l:addr} (pf: GEVEC_v (a, 0, d, l)):<prf> void
// end of [GEVEC_v_unnil]

prfun GEVEC_v_cons
  {a:viewt@ype}
  {n:pos} {d:inc} {l:addr} {ofs:int} (
    pf_mul: MUL (d, sizeof a, ofs), pf_at: a @ l, pf_vec: GEVEC_v (a, n-1, d, l+ofs)
  ) :<prf> GEVEC_v (a, n, d, l)
// end of [GEVEC_v_cons]

prfun GEVEC_v_uncons
  {a:viewt@ype}
  {n:pos} {d:inc} {l:addr} {ofs:int} (
    pf_mul: MUL (d, sizeof a, ofs), pf_vec: GEVEC_v (a, n, d, l)
  ) :<prf> (
    a @ l, GEVEC_v (a, n-1, d, l+ofs)
  )
// end of [GEVEC_v_uncons]

(* ****** ****** *)

prfun array_v_of_GEVEC_v
  {a:viewt@ype} {n:nat} {l:addr}
  (pf: GEVEC_v (a, n, 1, l)):<prf> array_v (a, n, l)
// end [array_v_of_GEVEC_v]

prfun GEVEC_v_of_array_v
  {a:viewt@ype} {n:nat} {l:addr}
  (pf: array_v (a, n, l)):<prf> GEVEC_v (a, n, 1, l)
// end [array_v_of_GEVEC_v]

(* ****** ****** *)

fun{a:viewt@ype} GEVEC_ptr_takeout
  {n:nat} {d:inc} {l0:addr} (
    pf: GEVEC_v (a, n, d, l0)
  | p_vec: ptr l0, d: int d, i: natLt n
  ) :<> [l:addr] (
    a @ l
  , a @ l -<lin,prf> GEVEC_v (a, n, d, l0)
  | ptr l
  )
// end of [GEVEC_ptr_takeout]

(* ****** ****** *)

stadef tszeq
  (a1:viewt@ype, a2:viewt@ype) = (sizeof a1 == sizeof a2)
// end of [tszeq]

fun{a1:viewt@ype}
  GEVEC_ptr_split
  {n,i:nat | i <= n} {d:inc} {l0:addr} (
    pf: GEVEC_v (a1, n, d, l0)
  | p_vec: ptr l0, d: int d, i: int i
  ) :<> [l:addr] (
    GEVEC_v (a1, i, d, l0)
  , GEVEC_v (a1, n-i, d, l)
  , {a2:viewt@ype | a1 \tszeq a2}
      (GEVEC_v (a2, i, d, l0), GEVEC_v (a2, n-i, d, l)) -<prf> GEVEC_v (a2, n, d, l0)
  | ptr l
  )
// end of [GEVEC_ptr_split]

(* ****** ****** *)

fun{a:t@ype} GEVEC_ptr_get_elt_at {n:nat}
  {d:inc} (V: &GEVEC (a, n, d), d: int d, i: natLt n):<> a
// end of [GEVEC_ptr_get_elt_at]

fun{a:t@ype} GEVEC_ptr_set_elt_at {n:nat}
  {d:inc} (V: &GEVEC (a, n, d), d: int d, i: natLt n, x: a):<> void
// end of [GEVEC_ptr_set_elt_at]

(* ****** ****** *)

fun{a:t@ype}
  GEVEC_ptr_initialize_elt {m:nat} {incX:inc} (
    X: &GEVEC (a?, m, incX) >> GEVEC (a, m, incX)
  , m: int m
  , incX: int incX
  , alpha: a
  ) :<> void
// end of [GEVEC_ptr_initialize_elt]

(* ****** ****** *)

fun GEVEC_ptr_foreach_fun_tsz__main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {d:inc} (
    pf: !v
  | base: &GEVEC (a, n, d)
  , f: (!v | &a, !vt) -<> void
  , vsz: int n
  , inc: int d
  , tsz: sizeof_t a
  , env: !vt
  ) :<> void
  = "atslib_GEVEC_ptr_foreach_fun_tsz__main"
// end of [fun]

fun{a:viewt@ype} GEVEC_ptr_foreach_fun
  {v:view} {n:nat} {d:inc} (
    pf: !v
  | base: &GEVEC (a, n, d)
  , f: (!v | &a) -<fun> void, vsz: int n, inc: int d
  ) :<> void
// end of [fun]

fun{a:viewt@ype} GEVEC_ptr_foreach_clo
  {v:view} {n:nat} {d:inc} (
    pf: !v
  | base: &GEVEC (a, n, d)
  , f: &(!v | &a) -<clo> void, vsz: int n, inc: int d
  ) :<> void
// end of [fun]

(* ****** ****** *)

fun GEVEC_ptr_iforeach_fun_tsz__main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {d:inc} (
    pf: !v
  | base: &GEVEC (a, n, d)
  , f: (!v | natLt n, &a, !vt) -<> void
  , vsz: int n
  , inc: int d
  , tsz: sizeof_t a
  , env: !vt
  ) :<> void
  = "atslib_GEVEC_ptr_iforeach_fun_tsz__main"
// end of [fun]

fun{a:viewt@ype}
  GEVEC_ptr_iforeach_fun {v:view} {n:nat} {d:inc} (
    pf: !v
  | base: &GEVEC (a, n, d)
  , f: (!v | natLt n, &a) -<fun> void, vsz: int n, inc: int d
  ) :<> void
// end of [fun]

fun GEVEC_ptr_iforeach_clo_tsz__main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {d:inc} (
    pf: !v
  | base: &GEVEC (a, n, d)
  , f: &(!v | natLt n, &a, !vt) -<clo> void
  , vsz: int n
  , inc: int d
  , tsz: sizeof_t a
  , env: !vt
  ) :<> void
  = "atslib_GEVEC_ptr_iforeach_clo_tsz__main"
// end of [fun]

fun{a:viewt@ype}
  GEVEC_ptr_iforeach_clo {v:view} {n:nat} {d:inc} (
    pf: !v
  | base: &GEVEC (a, n, d)
  , f: &(!v | natLt n, &a) -<clo> void, vsz: int n, inc: int d
  ) :<> void
// end of [fun]

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

datasort transpose =
  | TPN
  | TPT
  | TPC

(*

dataprop
transpose_NT (transpose) =
  | TRANSPOSE_NT_N (TPN) of ()
  | TRANSPOSE_NT_T (TPT) of ()
// end of [transpose_NT]

dataprop
transpose_NC (transpose) =
  | TRANSPOSE_NC_N (TPN) of ()
  | TRANSPOSE_NC_C (TPC) of ()
// end of [transpose_NC]

*)

datatype
TRANSPOSE (transpose) =
  | TRANSPOSE_N (TPN) of ()
  | TRANSPOSE_T (TPT) of ()
  | TRANSPOSE_C (TPC) of ()
// end of [TRANSPOSE]

(* ****** ****** *)

(*
** capturing the relation between transpose and order
*)
dataprop tranord_p (order, order) =
  | TRANORDrowcol (row, col) | TRANORDcolrow (col, row)
// end of [tranord_p]

(* ****** ****** *)

(*
** capturing the relation between transpose and dimensions
*)
dataprop trandim_p (
  transpose
, int // row
, int // col
, int // new row
, int // new col
) =
  | {m,n:nat} TRANDIM_N (TPN, m, n, m, n) of ()
  | {m,n:nat} TRANDIM_T (TPT, m, n, n, m) of ()
  | {m,n:nat} TRANDIM_C (TPC, m, n, n, m) of ()
(*
  | {m,n:nat} TRANDIM_AC (AC, m, n, m, n) of ()
*)
// end of [trandim_p]

(* ****** ****** *)

datasort side = left | right
datatype SIDE (side) = SIDEleft (left) | SIDEright (right)

(* ****** ****** *)

(*
** capturing the relation between side and row/col
*)
dataprop sidedim_p (
  side, int(*row*), int(*col*), int(*row/col*)
) =
  | {m,n:nat} SIDEDIM_L (left, m, n, m)
  | {m,n:nat} SIDEDIM_R (right, m, n, n)
// end of [sidedim_p]

(* ****** ****** *)

//
// GEneral MATrix representation
//

// elt, row, col, ord, lda
absviewt@ype GEMAT
  (a:viewt@ype+, m:int, n:int, ord:order, lda:int)
// end of [GEMAT]

viewdef GEMAT_v
  (a:viewt@ype, m:int, n:int, ord: order, lda:int, l:addr) =
  GEMAT (a, m, n, ord, lda) @ l
// end of [GEMAT_v]

(* ****** ****** *)

prfun GEMAT_v_trans
  {a:viewt@ype} {ord1:order}
  {m,n:nat} {lda:inc} {l:addr} (
    pf_mat: !GEMAT_v (a, m, n, ord1, lda, l) >>
             GEMAT_v (a, n, m, ord2, lda, l)
    // end of [pf_mat]
  ) :<> #[ord2:order] tranord_p (ord1, ord2)
// end of [GEMAT_v_trans]

(* ****** ****** *)

dataprop MATVECINC (order, order, int, int) =
  | {ld:inc} MATVECINCrowrow (row, row, ld, 1)
  | {ld:inc} MATVECINCrowcol (row, col, ld, ld)
  | {ld:inc} MATVECINCcolrow (col, row, ld, ld)
  | {ld:inc} MATVECINCcolcol (col, col, ld, 1)

// implemented in [genarrays.dats]
fun MATVECINC_get
  {ord1,ord2:order} {ld:int} {d:inc} (
    pf: MATVECINC (ord1, ord2, ld, d)
  | x1: ORDER ord1, x2: ORDER ord2, ld: int ld
  ) :<> int d

(* ****** ****** *)

prfun GEMAT_v_row_nil {a:viewt@ype}
  {n:nat} {ord:order} {ld:inc} {l:addr}
  () :<prf> GEMAT_v (a, 0, n, ord, ld, l)

prfun GEMAT_v_row_unnil {a:viewt@ype}
  {n:nat} {ord:order} {ld:inc} {l:addr}
  (pf: GEMAT_v (a, 0, n, ord, ld, l)) :<prf> void

prfun GEMAT_v_col_nil {a:viewt@ype}
  {m:nat} {ord:order} {ld:inc} {l:addr}
  () :<prf> GEMAT_v (a, m, 0, ord, ld, l)

prfun GEMAT_v_col_unnil {a:viewt@ype}
  {m:nat} {ord:order} {ld:inc} {l:addr}
  (pf: GEMAT_v (a, m, 0, ord, ld, l)) :<prf> void

(* ****** ****** *)

prfun GEMAT_v_uncons_row
  {a:viewt@ype} {m:pos;n:nat}
  {ord:order} {ld:inc} {l:addr}
  (pf: GEMAT_v (a, m, n, ord, ld, l))
  :<prf> [d: inc] (
    MATVECINC (row, ord, ld, d)
  , GEVEC_v (a, n, d, l)
  , GEVEC_v (a, n, d, l) -<lin,prf> GEMAT_v (a, m, n, ord, ld, l)
  )
// end of [GEMAT_uncons_col]

prfun GEMAT_v_uncons_col
  {a:viewt@ype} {m:nat;n:pos}
  {ord:order} {ld:inc} {l:addr}
  (pf: GEMAT_v (a, m, n, ord, ld, l))
  :<prf> [d: inc] (
    MATVECINC (col, ord, ld, d)
  , GEVEC_v (a, m, d, l)
  , GEVEC_v (a, m, d, l) -<lin,prf> GEMAT_v (a, m, n, ord, ld, l)
  )
// end of [GEMAT_v_uncons_col]

(* ****** ****** *)

prfun GEVEC_v_of_GEMAT_v_row
  {a1:viewt@ype} {ord:order} {n:nat} {ld:inc} {l:addr} (
    pf: GEMAT_v (a1, 1, n, ord, ld, l), ord: ORDER ord, ld: int ld
  ) :<> [d:inc] (
    MATVECINC (row, ord, ld, d)
  , GEVEC_v (a1, n, d, l)
  , {a2:viewt@ype | a1 \tszeq a2}
      GEVEC_v (a2, n, d, l) -<prf> GEMAT_v (a2, 1, n, ord, ld, l)
  // [fpf: for unsplitting]
  )
// end of [GEVEC_v_of_GEMAT_v_row]

prfun GEVEC_v_of_GEMAT_v_col
  {a1:viewt@ype}
  {ord:order} {m:nat} {ld:inc} {l:addr} (
    pf: GEMAT_v (a1, m, 1, ord, ld, l), ord: ORDER ord, ld: int ld
  ) :<> [d:inc] (
    MATVECINC (col, ord, ld, d)
  , GEVEC_v (a1, m, d, l)
  , {a2:viewt@ype | a1 \tszeq a2}
      GEVEC_v (a2, m, d, l) -<prf> GEMAT_v (a2, m, 1, ord, ld, l)
  // [fpf: for unsplitting]
  )
// end of [GEVEC_v_of_GEMAT_v_col]

(* ****** ****** *)

fun{a:viewt@ype} GEMAT_ptr_takeout
  {m,n:nat} {ord:order} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | ord: ORDER ord
  , p_mat: ptr l0
  , lda: int lda
  , i: natLt m, j: natLt n
  ) :<> [l:addr] (
    a @ l
  , a @ l -<lin,prf> GEMAT_v (a, m, n, ord, lda, l0)
  | ptr l
  )
// end of [GEMAT_ptr_takeout]

(* ****** ****** *)

fun{a:t@ype} GEMAT_ptr_get_elt_at
  {m,n:nat} {ord:order} {lda:inc} (
    ord: ORDER ord
  , A: &GEMAT (a, m, n, ord, lda)
  , lda: int lda
  , i: natLt m, j: natLt n
  ) :<> a
  = "atslib_GEMAT_ptr_get_elt_at"
// end of [GEMAT_ptr_get_elt_at]

fun{a:t@ype} GEMAT_ptr_set_elt_at
  {m,n:nat} {ord:order} {lda:inc} (
    ord: ORDER ord
  , A: &GEMAT (a, m, n, ord, lda)
  , lda: int lda
  , i: natLt m, j: natLt n
  , x: a
  ) :<> void 
  = "atslib_GEMAT_ptr_set_elt_at"
// end of [GEMAT_ptr_set_elt_at]

(* ****** ****** *)

(*
** this is likely to be slightly more efficient than GEMAT_ptr_split2x1
*)
fun{a:viewt@ype} GEMAT_ptr_tail_row
  {m:pos;n:nat} {ord:order} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | ord: ORDER ord
  , p_mat: ptr l0
  , lda: int lda
  ) :<> [l:addr] (
    GEMAT_v (a, m-1, n, ord, lda, l)
  , GEMAT_v (a, m-1, n, ord, lda, l) -<lin,prf> GEMAT_v (a, m, n, ord, lda, l0)
  | ptr l
  )
// end of [GEMAT_ptr_tail_row]

(*
** this is likely to be slightly more efficient than GEMAT_ptr_split1x2
*)
fun{a:viewt@ype} GEMAT_ptr_tail_col
  {m:nat;n:pos} {ord:order} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a, m, n, ord, lda, l0)
  | ord: ORDER ord
  , p_mat: ptr l0
  , lda: int lda
  ) :<> [l:addr] (
    GEMAT_v (a, m, n-1, ord, lda, l)
  , GEMAT_v (a, m, n-1, ord, lda, l) -<lin,prf> GEMAT_v (a, m, n, ord, lda, l0)
  | ptr l
  )
// end of [GEMAT_ptr_tail_col]

(* ****** ****** *)

viewtypedef GEMAT_ptr_split1x2_res_t (
  a1:viewt@ype, m:int, n:int, j:int, ord:order, lda:int, l0:addr
) = [l1,l2:addr] @(
  GEMAT_v (a1, m, j, ord, lda, l1)  
, GEMAT_v (a1, m, n-j, ord, lda, l2)
, {a2:viewt@ype | a1 \tszeq a2}
    (GEMAT_v (a2, m, j, ord, lda, l1), GEMAT_v (a2, m, n-j, ord, lda, l2)) -<prf>
    GEMAT_v (a2, m, n, ord, lda, l0)
  // [fpf: for unsplitting]
| ptr l1 // l1 should equal l0
, ptr l2
) // end of [GEMAT_ptr_split1x2_res_t]

fun{a1:viewt@ype} GEMAT_ptr_split1x2
  {m,n:nat} {j:nat | j <= n} {ord:order} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a1, m, n, ord, lda, l0)
  | ord: ORDER ord, p_mat: ptr l0, lda: int lda, j: int j
  ) :<> GEMAT_ptr_split1x2_res_t (a1, m, n, j, ord, lda, l0)
// end of [GEMAT_ptr_split1x2]

(* ****** ****** *)

viewtypedef GEMAT_ptr_split2x1_res_t (
  a1:viewt@ype, m:int, n:int, i:int, ord:order, lda:int, l0:addr
) = [l1,l2:addr] @(
  GEMAT_v (a1, i, n, ord, lda, l1)  
, GEMAT_v (a1, m-i, n, ord, lda, l2)
, {a2:viewt@ype | a1 \tszeq a2} (
    GEMAT_v (a2, i, n, ord, lda, l1)
  , GEMAT_v (a2, m-i, n, ord, lda, l2)
  ) -<prf>
    GEMAT_v (a2, m, n, ord, lda, l0)
  // [fpf: for unsplitting]
| ptr l1 // l1 should equal l0
, ptr l2
) // end of [GEMAT_ptr_split2x1_res_t]

fun{a1:viewt@ype} GEMAT_ptr_split2x1
  {m,n:nat} {i:nat | i <= m} {ord:order} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a1, m, n, ord, lda, l0)
  | ord: ORDER ord, p_mat: ptr l0, lda: int lda, i: int i
  ) :<> GEMAT_ptr_split2x1_res_t (a1, m, n, i, ord, lda, l0)
// end of [GEMAT_ptr_split2x1]

(* ****** ****** *)

viewtypedef GEMAT_ptr_split2x2_res_t (
  a1:viewt@ype, m:int, n:int, i:int, j:int, ord:order, lda:int, l0:addr
) = [l11,l12,l21,l22:addr] @(
  GEMAT_v (a1, i, j, ord, lda, l11)  
, GEMAT_v (a1, i, n-j, ord, lda, l12)
, GEMAT_v (a1, m-i, j, ord, lda, l21)
, GEMAT_v (a1, m-i, n-j, ord, lda, l22)
, {a2:viewt@ype | tszeq(a1,a2)} (
    GEMAT_v (a2, i, j, ord, lda, l11)
  , GEMAT_v (a2, i, n-j, ord, lda, l12)
  , GEMAT_v (a2, m-i, j, ord, lda, l21)
  , GEMAT_v (a2, m-i, n-j, ord, lda, l22)
  ) -<prf>
    GEMAT_v (a2, m, n, ord, lda, l0)
  // [fpf: for unsplitting]
| ptr l11 // l11 should equal l0
, ptr l12
, ptr l21
, ptr l22
) // end of [GEMAT_ptr_split2x2_res_t]

fun{a1:viewt@ype}
  GEMAT_ptr_split2x2
  {m,n:nat} {i,j:nat | i <= m; j <= n} {ord:order} {lda:inc} {l0:addr} (
    pf_mat: GEMAT_v (a1, m, n, ord, lda, l0)
  | ord: ORDER ord, p_mat: ptr l0, lda: int lda, i: int i, j: int j
  ) :<> GEMAT_ptr_split2x2_res_t (a1, m, n, i, j, ord, lda, l0)
// end of [GEMAT_ptr_split2x2]

(* ****** ****** *)

fun{a:t@ype}
  GEMAT_row_ptr_allocfree
  {m,n:pos} (m: int m, n: int n)
  : [l:addr] (
    GEMAT (a?, m, n, row, n) @ l
  | ptr l
  , (GEMAT (a?, m, n, row, n) @ l | ptr l) -<lin> void
  )
// end of [GEMAT_row_ptr_allocfree]

fun{a:t@ype}
  GEMAT_col_ptr_allocfree
  {m,n:pos} (m: int m, n: int n)
  : [l:addr] (
    GEMAT (a?, m, n, col, m) @ l
  | ptr l
  , (GEMAT (a?, m, n, col, m) @ l | ptr l) -<lin> void
  )
// end of [GEMAT_col_ptr_allocfree]

(* ****** ****** *)

fun{a:t@ype}
  GEMAT_ptr_initialize_elt
  {ord:order} {m,n:nat} {ld:inc} (
    ord: ORDER ord
  , X: &GEMAT (a?, m, n, ord, ld) >> GEMAT (a, m, n, ord, ld)
  , m: int m, n: int n, ld: int ld
  , alpha: a
  ) :<> void
// end of [GEMAT_ptr_initialize_elt]

fun{a:t@ype}
  GEMAT_ptr_initialize_fun
  {v:view} {ord:order} {m,n:nat} {ld:inc} (
    pf: !v
  | ord: ORDER ord
  , X: &GEMAT (a?, m, n, ord, ld) >> GEMAT (a, m, n, ord, ld)
  , m: int m, n: int n, ld: int ld
  , f: (!v | natLt m, natLt n, &(a?) >> a) -<> void
  ) :<> void
// end of [GEMAT_ptr_initialize_fun]

(* ****** ****** *)

fun GEMAT_ptr_foreach_fun_tsz__main
  {a:viewt@ype} {v:view} {vt:viewtype}
  {ord1,ord2:order} {m,n:nat} {ld:inc} (
    pf: !v
  | ord1: ORDER ord1
  , M: &GEMAT (a, m, n, ord1, ld)
  , f: (!v | &a, !vt) -<fun> void
  , ord2: ORDER ord2
  , m: int m, n: int n, ld: int ld
  , tsz: sizeof_t a
  , env: !vt
  ) :<> void
// end of [GEMAT_ptr_foreach_fun_tsz__main]

fun{a:viewt@ype} GEMAT_ptr_foreach_fun
  {v:view} {ord1,ord2:order} {m,n:nat} {ld:inc} (
    pf: !v
  | ord1: ORDER ord1
  , M: &GEMAT (a, m, n, ord1, ld)
  , f: (!v | &a) -<fun> void
  , ord2: ORDER ord2
  , m: int m, n: int n, ld: int ld
  ) :<> void
// end of [GEMAT_ptr_foreach_fun]

fun{a:viewt@ype} GEMAT_ptr_foreach_clo
  {v:view} {ord1,ord2:order} {m,n:nat} {ld:inc} (
    pf: !v
  | ord1: ORDER ord1
  , M: &GEMAT (a, m, n, ord1, ld)
  , f: &(!v | &a) -<clo> void
  , ord2: ORDER ord2
  , m: int m, n: int n, ld: int ld
  ) :<> void
// end of [GEMAT_ptr_foreach_clo]

(* ****** ****** *)

fun GEMAT_ptr_iforeach_fun_tsz__main
  {a:viewt@ype} {v:view} {vt:viewtype}
  {ord1,ord2:order} {m,n:nat} {ld:inc} (
    pf: !v
  | ord1: ORDER ord1
  , M: &GEMAT (a, m, n, ord1, ld)
  , f: (!v | natLt m, natLt n, &a, !vt) -<fun> void
  , ord2: ORDER ord2
  , m: int m, n: int n, ld: int ld
  , tsz: sizeof_t a
  , env: !vt
  ) :<> void
// end of [GEMAT_ptr_iforeach_fun_tsz__main]

fun{a:viewt@ype} GEMAT_ptr_iforeach_fun
  {v:view} {ord1,ord2:order} {m,n:nat} {ld:inc} (
    pf: !v
  | ord1: ORDER ord1
  , M: &GEMAT (a, m, n, ord1, ld)
  , f: (!v | natLt m, natLt n, &a) -<fun> void
  , ord2: ORDER ord2
  , m: int m, n: int n, ld: int ld
  ) :<> void
// end of [GEMAT_ptr_iforeach_fun]

fun{a:viewt@ype} GEMAT_ptr_iforeach_clo
  {v:view} {ord1,ord2:order} {m,n:nat} {ld:inc} (
    pf: !v
  | ord1: ORDER ord1
  , M: &GEMAT (a, m, n, ord1, ld)
  , f: &(!v | natLt m, natLt n, &a) -<clo> void
  , ord2: ORDER ord2
  , m: int m, n: int n, ld: int ld
  ) :<> void
// end of [GEMAT_ptr_iforeach_clo]

(* ****** ****** *)

dataprop realtyp_p (a:t@ype) =
  | REALTYPfloat (float) of () | REALTYPdouble (double) of ()
// end of [TYPE_IS_REAL]

(* ****** ****** *)

//
// TRiangular MATrix representation (part of GEMAT)
//

// elt, row/col, ord, ul
absviewt@ype TRMAT // dimension: n x n
  (a:viewt@ype+, n:int, ord: order, ul: uplo, dg: diag, lda: int)
// end of [TRMAT]

viewdef TRMAT_v
  (a:viewt@ype, n:int, ord: order, ul: uplo, dg: diag, lda: int, l:addr) =
  TRMAT (a, n, ord, ul, dg, lda) @ l
// end of [TRMAT_v]

prfun TRMAT_v_of_GEMAT_v
  {a:viewt@ype} {n:nat}
  {ord:order} {ul:uplo} {dg:diag}
  {lda:inc} {l:addr} (
    pf: GEMAT_v (a, n, n, ord, lda, l)
  , Uplo: UPLO ul, Diag: DIAG dg
  ) :<> (
    TRMAT_v (a, n, ord, ul, dg, lda, l)
  , TRMAT_v (a, n, ord, ul, dg, lda, l) -<lin,prf> GEMAT_v (a, n, n, ord, lda, l)
  )
// end of [TRMAT_v_of_GEMAT_v]

(* ****** ****** *)

// UN: upper non-unit
fun{a:t@ype} TRMAT_UN_ptr_get_elt_at
   {m:nat} {i,j:nat | i <= j; j < m} {ord:order} {lda:inc} (
     ord: ORDER ord
   , A: &TRMAT (a, m, ord, upper, nonunit, lda)
   , lda: int lda
   , i: int i, j: int j
   ) :<> a
  = "atslib_GEMAT_ptr_get_elt_at"
// end of [TRMAT_UN_ptr_get_elt_at]

fun{a:t@ype} TRMAT_UN_ptr_set_elt_at
   {m:nat} {i,j:nat | i <= j; j < m} {ord:order} {lda:inc} (
     ord: ORDER ord
   , A: &TRMAT (a, m, ord, upper, nonunit, lda)
   , lda: int lda
   , i: int i, j: int j
   , x: a
   ) :<> void
  = "atslib_GEMAT_ptr_set_elt_at"
// end of [TRMAT_UN_ptr_set_elt_at]

// UU: upper unit
fun{a:t@ype} TRMAT_UU_ptr_get_elt_at
   {m:nat} {i,j:nat | i < j; j < m} {ord:order} {lda:inc} (
     ord: ORDER ord
   , A: &TRMAT (a, m, ord, upper, nonunit, lda)
   , lda: int lda
   , i: int i, j: int j
   ) :<> a
  = "atslib_GEMAT_ptr_get_elt_at"
// end of [TRMAT_UU_ptr_get_elt_at]

fun{a:t@ype} TRMAT_UU_ptr_set_elt_at
   {m:nat} {i,j:nat | i < j; j < m} {ord:order} {lda:inc} (
     ord: ORDER ord
   , A: &TRMAT (a, m, ord, upper, nonunit, lda)
   , lda: int lda
   , i: int i, j: int j
   , x: a
   ) :<> void
  = "atslib_GEMAT_ptr_set_elt_at"
// end of [TRMAT_UU_ptr_set_elt_at]

// LN: lower non-unit
fun{a:t@ype} TRMAT_LN_ptr_get_elt_at
   {m:nat} {i,j:nat | j <= i; i < m} {ord:order} {lda:inc} (
     ord: ORDER ord
   , A: &TRMAT (a, m, ord, upper, nonunit, lda)
   , lda: int lda
   , i: int i, j: int j
   ) :<> a
  = "atslib_GEMAT_ptr_get_elt_at"
// end of [TRMAT_LN_ptr_get_elt_at]

fun{a:t@ype} TRMAT_LN_ptr_set_elt_at
   {m:nat} {i,j:nat | j <= i; i < m} {ord:order} {lda:inc} (
     ord: ORDER ord
   , A: &TRMAT (a, m, ord, upper, nonunit, lda)
   , lda: int lda
   , i: int i, j: int j
   , x: a
   ) :<> void
  = "atslib_GEMAT_ptr_set_elt_at"
// end of [TRMAT_LN_ptr_set_elt_at]

// LU: lower unit
fun{a:t@ype} TRMAT_LU_ptr_get_elt_at
   {m:nat} {i,j:nat | j < i; i < m} {ord:order} {lda:inc} (
     ord: ORDER ord
   , A: &TRMAT (a, m, ord, upper, nonunit, lda)
   , lda: int lda
   , i: int i, j: int j
   ) :<> a
  = "atslib_GEMAT_ptr_get_elt_at"
// end of [TRMAT_LU_ptr_get_elt_at]

fun{a:t@ype} TRMAT_LU_ptr_set_elt_at
   {m:nat} {i,j:nat | j < i; i < m} {ord:order} {lda:inc} (
     ord: ORDER ord
   , A: &TRMAT (a, m, ord, upper, nonunit, lda)
   , lda: int lda
   , i: int i, j: int j
   , x: a
   ) :<> void
  = "atslib_GEMAT_ptr_set_elt_at"
// end of [TRMAT_LU_ptr_set_elt_at]

(* ****** ****** *)

viewtypedef TRMAT_ptr_split2x2_res_t (
  a1:viewt@ype, m:int, i:int, ord:order, ul:uplo, dg:diag, lda:int, l0:addr
) = [lu,lo,ll:addr] @(
  TRMAT_v (a1, i, ord, ul, dg, lda, lu)
, GEMAT_v (a1, i, m-i, ord, lda, lo)
, TRMAT_v (a1, m-i, ord, ul, dg, lda, ll)
, {a2:viewt@ype | tszeq(a1,a2)} (
    TRMAT_v (a2, i, ord, ul, dg, lda, lu)
  , GEMAT_v (a2, i, m-i, ord, lda, lo)
  , TRMAT_v (a2, m-i, ord, ul, dg, lda, ll)
  ) -<prf>
    TRMAT_v (a2, m, ord, ul, dg, lda, l0)
  // [fpf: for unsplitting]
| ptr lu // l11 should equal l0
, ptr lo
, ptr ll
) // end of [TRMAT_ptr_split2x2_res_t]

fun{a1:viewt@ype}
  TRMAT_ptr_split2x2 {m:nat} {i:nat | i <= m}
  {ord:order} {ul:uplo} {dg:diag} {lda:inc} {l0:addr} (
    pf_mat: TRMAT_v (a1, m, ord, ul, dg, lda, l0)
  | ord: ORDER ord, ul: UPLO ul, A: ptr l0, lda: int lda, i: int i
  ) :<> TRMAT_ptr_split2x2_res_t (a1, m, i, ord, ul, dg, lda, l0)
// end of [TRMAT_ptr_split2x2]

(* ****** ****** *)

//
// SYmmetric MATrix representation (part of GEMAT)
//

// elt, row/col, ord, ul
absviewt@ype SYMAT // dimension: n x n
  (a:viewt@ype+, n:int, ord: order, ul: uplo, lda: int)
// end of [SYMAT]

viewdef SYMAT_v
  (a:viewt@ype, n:int, ord: order, ul: uplo, lda: int, l:addr) =
  SYMAT (a, n, ord, ul, lda) @ l
// end of [SYMAT_v]

prfun SYMAT_v_of_GEMAT_v
  {a:viewt@ype} {n:nat}
  {ord:order} {ul:uplo} {lda:inc} {l:addr} (
    pf: GEMAT_v (a, n, n, ord, lda, l), Uplo: UPLO ul
  ) :<> (
    SYMAT_v (a, n, ord, ul, lda, l)
  , SYMAT_v (a, n, ord, ul, lda, l) -<lin,prf> GEMAT_v (a, n, n, ord, lda, l)
  )
// end of [SYMAT_v_of_GEMAT_v]

(* ****** ****** *)

//
// HErmitian matrix representation (* part of GEMAT *)
//

// elt, row/col, ord, ul
absviewt@ype HEMAT // dimension: n x n
  (a:viewt@ype+, n:int, ord: order, ul: uplo, lda: int)
// end of [HEMAT]

viewdef HEMAT_v
  (a:viewt@ype, n:int, ord: order, ul: uplo, lda: int, l:addr) =
  HEMAT (a, n, ord, ul, lda) @ l
// end of [HEMAT_v]

prfun HEMAT_v_of_SYMAT_v
  {a:t@ype} {n:nat}
  {ord:order} {ul:uplo} {lda:inc} {l:addr} (
    pf_typ: realtyp_p (a), pf_mat: SYMAT_v (a, n, ord, ul, lda, l)
  ) :<> HEMAT_v (a, n, ord, ul, lda, l)
// end of [HEMAT_v_of_SYMAT_v]

prfun SYMAT_v_of_HEMAT_v
  {a:t@ype} {n:nat}
  {ord:order} {ul:uplo} {lda:inc} {l:addr} (
    pf_typ: realtyp_p (a), pf_mat: HEMAT_v (a, n, ord, ul, lda, l)
  ) :<> SYMAT_v (a, n, ord, ul, lda, l)
// end of [SYMAT_v_of_HEMAT_v]

prfun HEMAT_v_of_GEMAT_v
  {a:viewt@ype} {n:nat}
  {ord:order} {ul:uplo} {lda:inc} {l:addr} (
    pf: GEMAT_v (a, n, n, ord, lda, l), Uplo: UPLO ul
  ) :<> (
    HEMAT_v (a, n, ord, ul, lda, l)
  , HEMAT_v (a, n, ord, ul, lda, l) -<lin,prf> GEMAT_v (a, n, n, ord, lda, l)
  )
// end of [HEMAT_v_of_GEMAT_v]

(* ****** ****** *)

//
// General Band MATrix representation
//

// elt, row, col, ord, lower-bandwidth, upper-bandwidth
absviewt@ype GBMAT // dimension: m x n, lower-bandwidth: kl, upper-bandwidth: ku
  (a:viewt@ype+, m:int, n:int, ord: order, kl: int, ku: int, lda: int)
// end of [GBMAT]

viewdef GBMAT_v
  (a:viewt@ype, m:int, n:int, ord: order, kl: int, ku: int, lda: int, l: addr) =
  GBMAT (a, m, n, ord, kl, ku, lda) @ l
// end of [GBMAT_v]

(* ****** ****** *)

//
// Triangular Band MATrix representation
//

// elt, row/col, ord, ul, diag, bandwidth
absviewt@ype TBMAT // dimension: n x n, bandwidth: k
  (a:viewt@ype+, n:int, ord: order, ul: uplo, dg: diag, k: int, lda: int)
// end of [TBMAT]

viewdef TBMAT_v
  (a:viewt@ype, n:int, ord: order, ul: uplo, dg: diag, k: int, lda: int, l: addr) =
  TBMAT (a, n, ord, ul, dg, k, lda) @ l

prfun TBMAT_v_of_GEMAT_v
  {a:viewt@ype} {n,k:nat}
  {ul:uplo} {dg:diag} {l:addr} (
    pf_gmat: GEMAT_v (a, 1+k, n, col, 1+k, l)
  , ul: UPLO ul
  , dg: DIAG dg
  , k: int k
  ) :<prf> (
    TBMAT_v (a, n, col, ul, dg, k, 1+k, l)
  , TBMAT_v (a, n, col, ul, dg, k, 1+k, l) -<prf> GEMAT_v (a, 1+k, n, col, 1+k, l)
  )
// end of [TBMAT_v_of_GEMAT_v]


(* ****** ****** *)

//
// Triangular Packed MATrix representation
//

// elt, row/col, ord, ul, diag
absviewt@ype TPMAT // dimension: n x n
  (a:viewt@ype+, n:int, ord: order, ul: uplo, dg: diag)
// end of [TPMAT]

viewdef TPMAT_v
  (a:viewt@ype, n:int, ord: order, ul: uplo, dg: diag, l: addr) =
  TPMAT (a, n, ord, ul, dg) @ l
// end of [TPMAT_v]

prfun TPMAT_v_of_GEVEC_v
  {a:viewt@ype} {m,n:nat}
  {ord:order} {ul:uplo} {dg:diag}
  {l:addr} (
    pf_mul: MUL (n, n+1, m+m)
  , pf_vec: GEVEC_v (a, m, 1, l)
  , ord: ORDER (ord)
  , ul: UPLO (ul), dg: DIAG (dg)
  ) :<> (
    TPMAT_v (a, n, ord, ul, dg, l)
  , TPMAT_v (a, n, ord, ul, dg, l) -<prf> GEVEC_v (a, m, 1, l)
  )
// end of [TPMAT_v_of_GEVEC_v]

(* ****** ****** *)

//
// Symmetric Band MATrix representation
//

// elt, row/col, ord, ul, band-width
absviewt@ype SBMAT // dimension: n x n
  (a:viewt@ype+, n:int, ord: order, ul: uplo, k:int, ld:int)
// end of [SBMAT]

viewdef SBMAT_v
  (a:viewt@ype, n:int, ord: order, ul: uplo, k:int, ld:int, l: addr) =
  SBMAT (a, n, ord, ul, k, ld) @ l
// end of [SBMAT_v]

(* ****** ****** *)

//
// Symmetric Packed MATrix representation
//

// elt, row/col, ord, ul, diag
absviewt@ype SPMAT // dimension: n x n
  (a:viewt@ype+, n:int, ord: order, ul: uplo)
// end of [SPMAT]

viewdef SPMAT_v
  (a:viewt@ype, n:int, ord: order, ul: uplo, l: addr) =
  SPMAT (a, n, ord, ul) @ l
// end of [SPMAT_v]

prfun SPMAT_v_of_GEVEC_v
  {a:viewt@ype} {m,n:nat}
  {ord:order} {ul:uplo}
  {l:addr} (
    pf_mul: MUL (n, n+1, m+m)
  , pf_arr: GEVEC_v (a, m, 1, l)
  , ord: ORDER (ord), ul: UPLO (ul)
  ) :<> (
    SPMAT_v (a, n, ord, ul, l)
  , SPMAT_v (a, n, ord, ul, l) -<prf> GEVEC_v (a, m, 1, l)
  )
// end of [HPMAT_v_of_GEVEC_v]

(* ****** ****** *)

//
// Hermitian Band MATrix representation
//

// elt, row/col, ord, ul, band-width
absviewt@ype HBMAT // dimension: n x n
  (a:viewt@ype+, n:int, ord: order, ul: uplo, k:int, ld:int)
// end of [HBMAT]

viewdef HBMAT_v
  (a:viewt@ype, n:int, ord: order, ul: uplo, k:int, ld:int, l: addr) =
  HBMAT (a, n, ord, ul, k, ld) @ l
// end of [HBMAT_v]

prfun HBMAT_v_of_SBMAT_v
  {a:t@ype} {n:nat}
  {ord:order} {ul:uplo} {k:int} {ld:int} {l:addr} (
    pf_typ: realtyp_p (a), pf_mat: SBMAT_v (a, n, ord, ul, k, ld, l)
  ) :<> HBMAT_v (a, n, ord, ul, k, ld, l)
// end of [HBMAT_v_of_SBMAT_v]

prfun SBMAT_v_of_HBMAT_v
  {a:t@ype} {n:nat}
  {ord:order} {ul:uplo} {k:int} {ld:int} {l:addr} (
    pf_typ: realtyp_p (a), pf_mat: HBMAT_v (a, n, ord, ul, k, ld, l)
  ) :<> SBMAT_v (a, n, ord, ul, k, ld, l)
// end of [SBMAT_v_of_HBMAT_v]

(* ****** ****** *)

//
// Hermitian Packed MATrix representation
//

// elt, row/col, ord, ul, diag
absviewt@ype HPMAT // dimension: n x n
  (a:viewt@ype+, n:int, ord: order, ul: uplo)
// end of [HPMAT]

viewdef HPMAT_v
  (a:viewt@ype, n:int, ord: order, ul: uplo, l: addr) =
  HPMAT (a, n, ord, ul) @ l
// end of [HPMAT_v]

prfun HPMAT_v_of_SPMAT_v
  {a:t@ype} {n:nat}
  {ord:order} {ul:uplo} {l:addr} (
    pf_typ: realtyp_p (a), pf_mat: SPMAT_v (a, n, ord, ul, l)
  ) :<> HPMAT_v (a, n, ord, ul, l)
// end of [HPMAT_v_of_SPMAT_v]

prfun SPMAT_v_of_HPMAT_v
  {a:t@ype} {n:nat}
  {ord:order} {ul:uplo} {l:addr} (
    pf_typ: realtyp_p (a), pf_mat: HPMAT_v (a, n, ord, ul, l)
  ) :<> SPMAT_v (a, n, ord, ul, l)
// end of [SPMAT_v_of_HPMAT_v]

prfun HPMAT_v_of_GEVEC_v
  {a:viewt@ype} {m,n:nat}
  {ord:order} {ul:uplo}
  {l:addr} (
    pf_mul: MUL (n, n+1, m+m)
  , pf_arr: GEVEC_v (a, m, 1, l)
  , ord: ORDER (ord), ul: UPLO (ul)
  ) :<> (
    HPMAT_v (a, n, ord, ul, l)
  , HPMAT_v (a, n, ord, ul, l) -<prf> GEVEC_v (a, m, 1, l)
  )
// end of [HPMAT_v_of_GEVEC_v]

(* ****** ****** *)

(* end of [genarrays.sats] *)
