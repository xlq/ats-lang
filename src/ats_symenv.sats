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

staload "ats_symbol.sats"

(* ****** ****** *)

absviewtype
symmap_t (itm: t@ype) // boxed type

fun{itm:t@ype} symmap_search
  (_: !symmap_t itm, _: symbol_t): Option_vt itm

fun{itm:t@ype} symmap_ref_search
  (_: ref (symmap_t itm), _: symbol_t): Option_vt itm

fun{itm:t@ype} symmap_list
  (_: !symmap_t itm): List_vt @(symbol_t, itm)

fun{itm:t@ype} symmap_ref_list
  (_: ref (symmap_t itm)): List_vt @(symbol_t, itm)

(* ****** ****** *)

abstype
symenv_t (itm: t@ype) // boxed type

(* ****** ****** *)

fun symenv_make {itm:t@ype} (): symenv_t (itm)

(* ****** ****** *)

fun{itm:t@ype} symenv_insert
  (_: symenv_t itm, _: symbol_t, _: itm): void
fun{itm:t@ype} symenv_remove
  (_: symenv_t itm, _: symbol_t): Option_vt itm

fun{itm:t@ype} symenv_search
  (_: symenv_t itm, _: symbol_t): Option_vt itm
fun{itm:t@ype} symenv_pervasive_search
  (_: symenv_t itm, _: symbol_t): Option_vt itm

(* ****** ****** *)

fun{itm:t@ype} symenv_pop (_: symenv_t itm): void
fun symenv_push {itm:t@ype} (_: symenv_t itm): void

(* ****** ****** *)

fun symenv_top {itm:t@ype} (_: symenv_t itm): symmap_t itm
fun symenv_ref_top
 {itm:t@ype} (_: symenv_t itm): ref (symmap_t itm)

(* ****** ****** *)

fun{itm:t@ype} symenv_localjoin (_: symenv_t itm): void

(* ****** ****** *)

fun symenv_save {itm:t@ype} (_: symenv_t itm): void
fun{itm:t@ype} symenv_restore (_: symenv_t itm): void

(* ****** ****** *)

fun symenv_pervasive_add
  {itm:t@ype} (_: symenv_t itm, _: symmap_t itm): void

(* ****** ****** *)

(* end of [ats_symenv.sats] *)
