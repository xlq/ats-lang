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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

//
// some common functions that iterate over natural numbers;
// The code mainly serves as an example for writing iterative loops
// in ATS
//

(* ****** ****** *)

fun foreach_main {v:view} {vt: viewtype} {n:nat} {f:eff}
  (pf: !v | n: int n, f: (!v | natLt n, !vt) -<f> void, env: !vt):<f> void

fun foreach_fun {v:view} {n:nat} {f:eff}
  (pf: !v | n: int n, f: (!v | natLt n) -<f> void):<f> void

fun foreach_clo {v:view} {n:nat} {f:eff}
  (pf: !v | n: int n, f: &(!v | natLt n) -<clo,f> void):<f> void

// this one is the usual functional version
fun foreach_cloref {n:nat} {f:eff}
  (n: int n, f: (natLt n) -<cloref,f> void):<f> void

(* ****** ****** *)

fun foreach2_main {v:view} {vt: viewtype} {m,n:nat} {f:eff} (
    pf: !v
  | m: int m, n: int n
  , f: (!v | natLt m, natLt n, !vt) -<f> void
  , env: !vt
  ) :<f> void

fun foreach2_fun {v:view} {m,n:nat} {f:eff}
  (pf: !v | m: int m, n: int n, f: (!v | natLt m, natLt n) -<f> void) :<f> void

fun foreach2_clo {v:view} {m,n:nat} {f:eff}
  (pf: !v | m: int m, n: int n, f: &(!v | natLt m, natLt n) -<clo,f> void) :<f> void

// this one is the usual functional version
fun foreach2_cloref {m,n:nat} {f:eff}
  (m: int m, n: int n, f: (natLt m, natLt n) -<cloref,f> void) :<f> void
// end of [foreach2_cloref]

(* ****** ****** *)

fun repeat_main {v:view} {vt:viewtype} {n:nat} {f:eff}
  (pf: !v | n: int n, f: (!v | !vt) -<f> void, env: !vt):<f> void

fun repeat_fun {v:view} {n:nat} {f:eff}
  (pf: !v | n: int n, f: (!v | (*none*)) -<f> void):<f> void

fun repeat_clo {v:view} {n:nat} {f:eff}
  (pf: !v | n: int n, f: &(!v | (*none*)) -<clo,f> void):<f> void

fun repeat_cloref
  {n:nat} {f:eff} (n: int n, f: () -<cloref,f> void):<f> void
// end of [repeat_cloref]

(* ****** ****** *)

(* end of [iterint.sats] *)
