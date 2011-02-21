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
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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

%{#
#include "contrib/linux/CATS/linux/slab.cats"
%} // end of [%{#]

(* ****** ****** *)

absview kfree_v (n:int, l:addr)

(* ****** ****** *)

dataview
kmalloc_v (n:int, addr) =
  | {l:agz}
    kmalloc_v_succ (n, l) of (kfree_v (n, l), b0ytes n @ l)
  | kmalloc_v_fail (n, null) of ()
// end of [kmalloc_v]

fun kmalloc {n:nat} (
  n: size_t n, flags: int
) :<> [l:addr] (kmalloc_v (n, l) | ptr l) = "atsctrb_linux_kmalloc"
// end of [kmalloc]

(* ****** ****** *)

fun kfree {n:nat} {l:addr} (
  pf1: kfree_v (n, l), pf2: b0ytes (n) @ l | p: ptr l
) : void = "atsctrb_linux_kfree" // end of [kfree]

(* ****** ****** *)

(* end of [slab.sats] *)
