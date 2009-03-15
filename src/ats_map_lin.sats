(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
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

// Time: October 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

// A linear map implementation based on randomized binary search trees

(* ****** ****** *)

absviewtype map_vt (key: t@ype, itm: t@ype) // boxed type

(* ****** ****** *)

fun map_make {key,itm:t@ype}
  (cmp: (key, key) -<fun> Sgn):<> map_vt (key, itm)

// free up the map
fun{key,itm:t@ype} map_free (m: map_vt (key, itm)):<> void

// clean up the map
fun{key,itm:t@ype} map_clean (m: !map_vt (key, itm)):<> void

(* ****** ****** *)

fun{key,itm:t@ype} map_insert (m: !map_vt (key, itm), k: key, i: itm):<> void
fun{key,itm:t@ype} map_remove (m: !map_vt (key, itm), k: key):<> Option_vt itm

fun{key,itm:t@ype} map_search (m: !map_vt (key, itm), k: key):<> Option_vt itm

fun{key,itm:t@ype} map_join
  (m1: map_vt (key, itm), m2: map_vt (key, itm)):<> map_vt (key, itm)

(* ****** ****** *)

// list a map in pre-order
fun{key,itm:t@ype} map_list_pre (m: !map_vt (key, itm)):<> List_vt @(key, itm)

fun{key,itm:t@ype} map_foreach_pre {v:view} {vt:viewtype} {f:eff} (
    pf: !v
  | m: !map_vt (key, itm)
  , f: (!v | key, itm, !vt) -<f> void
  , env: !vt
  ) :<f> void

(* ****** ****** *)

(* end of [ats_map_lin.sats] *)
