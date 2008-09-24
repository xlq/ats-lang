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
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
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

// some common functions that iterate over integers

fun foreach_main {v:view} {vt: viewtype} {n:nat} {f:eff}
  (pf: !v | n: int n, f: (!v | natLt n, !vt) -<f> void, env: !vt):<f> void

fun foreach_fun {n:nat} {f:eff}
  (f: int n, f: !natLt n -<f> void):<f> void

fun foreach_cloptr {n:nat} {f:eff}
  (f: int n, f: !natLt n -<cloptr,f> void):<f> void

(* ****** ****** *)

fun foreach2_main {v:view} {vt: viewtype} {m,n:nat} {f:eff} (
    pf: !v
  | m: int m, n: int n
  , f: (!v | natLt m, natLt n, !vt) -<f> void
  , env: !vt
  ) :<f> void

fun foreach2_fun {m,n:nat} {f:eff}
  (m: int m, n: int n, f: (natLt m, natLt n) -<f> void) :<f> void

fun foreach2_cloptr {m,n:nat} {f:eff}
  (m: int m, n: int n, f: !(natLt m, natLt n) -<cloptr,f> void) :<f> void

(* ****** ****** *)

fun repeat_main {v:view} {vt:viewtype} {n:nat} {f:eff}
  (pf: !v | n: int n, f: (!v | !vt) -<f> void, env: !vt):<f> void

fun repeat_fun {n:nat} {f:eff} (n: int n, f: () -<f> void):<f> void
fun repeat_cloptr {n:nat} {f:eff} (n: int n, f: !() -<cloptr,f> void):<f> void

(* ****** ****** *)

(* end of [iterint.sats] *)
