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

#if VERBOSE_PRELUDE #then

#print "Loading [matrix.sats] starts!\n"

#endif

(* ****** ****** *)

(*
 *
 *
 * persistent matrices
 *
 *
 *)

(* ****** ****** *)

fun matrix {a:viewt@ype} {m,n:int}
  (m: int m, n: int n):<> arraysize (a, m * n) -<cloptr> matrix (a, m, n)
  = "atspre_matrix_main"

fun matrix_main {a:viewt@ype} {m,n,mn:int} (m: int m, n: int n)
  :<> (MUL (m, n, mn) | arraysize (a, mn)) -<cloptr> matrix (a, m, n)
  = "atspre_matrix_main"

(* ****** ****** *)

fun{a:t@ype} matrix_make_elt {m,n:pos}
  (row: int m, col: int n, elt: a):<> matrix (a, m, n)

fun matrix_make_fun_tsz_main
  {a:viewt@ype} {v:view} {vt:viewtype} {m,n:pos} {f:eff} (
    pf: !v
  | row: int m, col: int n
  , f: (!v | &(a?) >> a, natLt m, natLt n, !vt) -<f> void
  , tsz: sizeof_t a
  , env: !vt
  ) :<f> matrix (a, m, n)

fun matrix_make_fun_tsz_cloptr {a:viewt@ype} {m,n:pos} {f:eff} (
    row: int m, col: int n
  , f: !(&(a?) >> a, natLt m, natLt n) -<cloptr,f> void
  , tsz: sizeof_t a
  ) :<f> matrix (a, m, n)

(* ****** ****** *)

fun{a:t@ype} matrix_get_elt_at {m,n:nat}
  (A: matrix (a, m, n), i: natLt m, n: int n, j: natLt n):<!ref> a
fun{a:t@ype} matrix_set_elt_at {m,n:nat}
  (A: matrix (a, m, n), i: natLt m, n: int n, j: natLt n, x: a):<!ref> void

overload [] with matrix_get_elt_at
overload [] with matrix_set_elt_at

(* ****** ****** *)

fun{a:t@ype} foreach_matrix_main
  {v:view} {vt:viewtype} {m,n:nat} {f:eff} (
    pf: !v
  | f: (!v | a, !vt) -<fun,f> void
  , M: matrix (a, m, n), m: int m, n: int n
  , env: !vt
  ) :<f,!ref> void
overload foreach with foreach_matrix_main

fun{a:t@ype} foreach_matrix_cloptr {m,n:nat} {f:eff}
  (f: !(a -<cloptr,f> void), M: matrix (a, m, n), m: int m, n: int n)
  :<f,!ref> void
overload foreach with foreach_matrix_cloptr

fun{a:t@ype} foreach_matrix_cloref {m,n:nat} {f:eff}
  (f: !(a -<cloref,f> void), M: matrix (a, m, n), m: int m, n: int n)
  :<f,!ref> void
overload foreach with foreach_matrix_cloref

(* ****** ****** *)

fun{a:t@ype} iforeach_matrix_main
  {v:view} {vt:viewtype} {m,n:nat} {f:eff} (
    pf: !v
  | f: (!v | natLt m, natLt n, a, !vt) -<fun,f> void
  , M: matrix (a, m, n), m: int m, n: int n
  , env: !vt
  ) :<f,!ref> void
overload iforeach with iforeach_matrix_main

fun{a:t@ype} iforeach_matrix_cloptr {m,n:nat} {f:eff} (
    f: !(natLt m, natLt n, a) -<cloptr,f> void
  , M: matrix (a, m, n), m: int m, n: int n
  ) :<f,!ref> void
overload iforeach with iforeach_matrix_cloptr

fun{a:t@ype} iforeach_matrix_cloref {m,n:nat} {f:eff} (
    f: !(natLt m, natLt n, a) -<cloref,f> void
  , M: matrix (a, m, n), m: int m, n: int n
  ) :<f,!ref> void
overload iforeach with iforeach_matrix_cloptr

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [matrix.sats] finishes!\n"

#endif

(* end of [matrix.sats] *)
