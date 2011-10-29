(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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

(*
**
** A ordered set implementation
** based on randomized binary search trees
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2011
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

staload "libats/SATS/linordset_randbst.sats"

(* ****** ****** *)

extern
fun linordset_rngobj_eval
  (obj: !rngobj):<> double = "atslib_linordset_rngobj_eval"
// end of [linordset_rngobj_eval]

(* ****** ****** *)

fn randchoose
  {m,n:nat} (
  obj: !rngobj, m: int m, n: int n
) :<> natLt (2) = let
  val r = linordset_rngobj_eval (obj)
in
  if (m+n) * r <= (double_of)m then 0 else 1
end // end of [randchoose]

(* ****** ****** *)

(* end of [linordset_randbst.dats] *)
