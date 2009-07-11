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

absviewt@ype
  fmatrix_viewt0ype_int_int_viewt0ype (a:viewt@ype,row:int,col:int)
// [end of fmatrix_viewt0ype_int_int_viewt0ype]

stadef fmatrix = fmatrix_viewt0ype_int_int_viewt0ype
viewdef fmatrix_v
  (a:viewt@ype, row:int, col:int, l:addr) = fmatrix (a, row, col) @ l
// end of [fmatrix_v]

(* ****** ****** *)

prfun array_v_of_fmatrix_v
  {a:viewt@ype} {m,n:int} {l:addr}
  (pf_mat: fmatrix_v (a, m, n, l))
  :<> [mn:int] (MUL (m, n, mn), array_v (a, mn, l))
// end of [array_v_of_fmatrix_v]

prfun fmatrix_v_of_array_v
  {a:viewt@ype} {m,n:int} {mn:int} {l:addr}
  (pf_mul: MUL (m, n, mn), pf_arr: array_v (a, mn, l))
  :<> fmatrix_v (a, m, n, l)
// end of [fmatrix_v_of_array_v]

(* ****** ****** *)

fun{a:t@ype}
fmatrix_ptr_initialize_elt
  {m,n:nat} {l:addr} (
    base: &fmatrix (a?, m, n) >> fmatrix (a, m, n)
  , m: int m, n: int n, x: &a
  ) :<> void
// end of [fmatrix_initialize_elt]

fun
fmatrix_ptr_initialize_elt_tsz
  {a:t@ype} {m,n:nat} {l:addr} (
    base: &fmatrix (a?, m, n) >> fmatrix (a, m, n)
  , m: int m, n: int n, x: &a, tsz: sizeof_t a
  ) :<> void
// end of [fmatrix_initialize_elt_tsz]

(* ****** ****** *)

fun{a:viewt@ype} fmatrix_ptr_initialize_clo
  {v:view} {m,n:nat} (
    pf: !v 
  | base: &fmatrix (a?, m, n) >> fmatrix (a, m, n)
  , m: int m, n: int n
  , f: &(!v | &(a?) >> a, natLt m, natLt n) -<clo> void
  ) :<> void
// end of [fmatrix_ptr_initialize_clo]

fun fmatrix_ptr_initialize_clo_tsz
  {a:viewt@ype} {v:view} {m,n:nat} (
    pf: !v 
  | base: &fmatrix (a?, m, n) >> fmatrix (a, m, n)
  , m: int m, n: int n
  , f: &(!v | &(a?) >> a, natLt m, natLt n) -<clo> void
  , tsz: sizeof_t a
  ) :<> void
// end of [fmatrix_ptr_initialize_clo_tsz]

(* ****** ****** *)

fun{a:viewt@ype} fmatrix_ptr_takeout
  {m,n:int} {i,j:nat | i < m; j < n} {l0:addr} (
    pf_mat: fmatrix_v (a, m, n, l0)
  | base: ptr l0, i: int i, m: int m, j: int j
  ) :<> [l:addr] (
    a @ l
  , a @ l -<lin,prf> fmatrix_v (a, m, n, l0)
  | ptr l
  )
(* end of [fmatrix_ptr_takeout] *)

fun fmatrix_ptr_takeout_tsz {a:viewt@ype}
  {m,n:int} {i,j:nat | i < m; j < n} {l0:addr} (
    pf_mat: fmatrix_v (a, m, n, l0)
  | base: ptr l0, i: int i, m: int m, j: int j, tsz: sizeof_t a
  ) :<> [l:addr] (
    a @ l
  , a @ l -<lin,prf> fmatrix_v (a, m, n, l0)
  | ptr l
  ) = "atslib_fmatrix_ptr_takeout_tsz"
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

prfun GEVEC_v_of_fmatrix_v
  {a:viewt@ype} {m,n:nat} {mn:nat} {l:addr} (
    pf_mul: MUL (m, n, mn), pf_mat: fmatrix_v (a, m, n, l)
  ) :<> (
    GEVEC_v (a, mn, 1, l)
  , GEVEC_v (a, mn, 1, l) -<prf> fmatrix_v (a, m, n, l)
  )
// end of [GEVEC_v_of_fmatrix_v]

(* ****** ****** *)

prfun GEMAT_v_of_fmatrix_v
  {a:viewt@ype} {m,n:nat} {l:addr} (
    pf_mat: fmatrix_v (a, m, n, l)
  ) :<> (
    GEMAT_v (a, m, n, col, m, l)
  , GEMAT_v (a, m, n, col, m, l) -<prf> fmatrix_v (a, m, n, l)
  )
// end of [GEMAT_v_of_fmatrix_v]

(* ****** ****** *)

prfun GBMAT_v_of_fmatrix_v
  {a:viewt@ype} {m,n,k,kl,ku:nat| k == kl+ku+1} {l:addr} (
    pf : fmatrix_v (a, k, n, l), m : int m, kl : int kl, ku : int ku
  ) :<> (
    GBMAT_v (a, m, n, col, kl, ku, k, l)
  , GBMAT_v (a, m, n, col, kl, ku, k, l) -<prf> fmatrix_v (a, k, n, l)
  )
// end of [GEBAT_v_of_fmatrix_v]

(* ****** ****** *)

fun fmatrix_ptr_foreach_fun_tsz__main
  {a:viewt@ype}
  {v:view} {vt:viewtype}
  {ord:order} {m,n:nat} (
    pf: !v
  | M: &fmatrix (a, m, n)
  , f: (!v | &a, !vt) -<fun> void
  , ord: ORDER ord, m: int m, n: int n
  , tsz: sizeof_t a
  , env: !vt
  ) :<> void
// end of [fmatrix_foreach_fun_tsz__main]

fun fmatrix_ptr_foreach_fun_tsz
  {a:viewt@ype} {v:view} {ord:order} {m,n:nat} (
    pf: !v
  | M: &fmatrix (a, m, n)
  , f: (!v | &a) -<fun> void
  , ord: ORDER ord, m: int m, n: int n
  , tsz: sizeof_t a
  ) :<> void
// end of [fmatrix_foreach_fun_tsz]

fun fmatrix_ptr_foreach_clo_tsz
  {a:viewt@ype} {v:view} {ord:order} {m,n:nat} (
    pf: !v
  | M: &fmatrix (a, m, n)
  , f: &(!v | &a) -<clo> void
  , ord: ORDER ord, m: int m, n: int n
  , tsz: sizeof_t a
  ) :<> void
// end of [fmatrix_foreach_clo_tsz]

(* ****** ****** *)

(* end of [fmatrix.sats] *)
