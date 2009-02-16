(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
**
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
**
*)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

abstype symbol_t // a boxed type for symbols

fun name_is_new (name: string): bool
fun symbol_make_name (name: string): symbol_t
fun symbol_make_newname (name: string): symbol_t

fun eq_symbol_symbol (x1: symbol_t, x2: symbol_t): bool
overload = with eq_symbol_symbol

fun neq_symbol_symbol (x1: symbol_t, x2: symbol_t): bool
overload <> with neq_symbol_symbol

fun compare_symbol_symbol (x1: symbol_t, x2: symbol_t): Sgn
overload compare with compare_symbol_symbol

fun symbol_is_term (x: symbol_t): bool // is terminal
fun symbol_is_nonterm (x: symbol_t): bool // is nonterminal

fun symbol_assoc_get (x: symbol_t): int
  = "atsyacc_symbol_assoc_get"
fun symbol_assoc_set (x: symbol_t, assoc: int): void
  = "atsyacc_symbol_assoc_set"

(* ****** ****** *)

(* end of [symbol.sats] *)
