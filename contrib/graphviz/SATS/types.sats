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
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
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
//
// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: October, 2011
//
(* ****** ****** *)

(*
typedef struct graph_t graph_t;
*)
viewtypedef graph_t =
  $extype_struct "graph_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef graph = graph_t

absviewtype
pgraph_viewtype (l:addr) = ptr
stadef pgraph = pgraph_viewtype
viewtypedef pgraph1 = [l:addr | l > null] pgraph (l)
//
fun agclose {l:agz}
  (g: pgraph l): void = "mac#atsctrb_agclose"
//
fun agread (
  filr: FILEref
) : pgraph1 = "mac#atsctrb_agread"
//
fun agwrite {l:agz}
  (g: !pgraph l, filr: FILEref): [i:int | i <= 0] int(*err*)
//
(* ****** ****** *)

(* end of [types.sats] *)
