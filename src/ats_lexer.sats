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

// July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "libats_lex_lexing.sats"

(* ****** ****** *)

staload "ats_posmark.sats"
staload "ats_location.sats"

(* ****** ****** *)

abst@ype token_t = $extype "ats_int_type"

(* ****** ****** *)

val ISNONE : token_t
val ISSTATIC : token_t and ISDYNAMIC : token_t

// implemented in [ats_lexer.lats]
fun eq_token_token (t1: token_t, t2: token_t): bool= "eq_token_token"
overload = with eq_token_token

(* ****** ****** *)

fun MAIN (): token_t = "ats_lexer_token_get"
fun token_is_valid (t: token_t): bool = "token_is_valid"

(* ****** ****** *)

(* end of [ats_lexer.sats] *)

