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

//

fun symbol_name_get (x: symbol_t): string

//

fun name_is_new (name: string): bool
fun symbol_find_name (name: string): Option_vt (symbol_t)

// terminal : knd = 0 / nonterm : knd = 1
datatype symkind = SYMKINDterm | SYMKINDnonterm

fun symbol_make_name (knd: symkind, name: string): symbol_t
fun symbol_make_newname (knd: symkind, name: string): symbol_t

//

val the_end_symbol : symbol_t // terminal
val the_accept_symbol : symbol_t // nonterm

//

fun eq_symbol_symbol (x1: symbol_t, x2: symbol_t):<> bool
overload = with eq_symbol_symbol

fun neq_symbol_symbol (x1: symbol_t, x2: symbol_t):<> bool
overload <> with neq_symbol_symbol

fun compare_symbol_symbol (x1: symbol_t, x2: symbol_t):<> Sgn
overload compare with compare_symbol_symbol

//

fun fprint_symbol {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, _: symbol_t): void

fun print_symbol (_: symbol_t): void
fun prerr_symbol (_: symbol_t): void

//

fun symbol_is_term (x: symbol_t):<> bool // is terminal
fun symbol_is_nonterm (x: symbol_t):<> bool // is nonterminal

fun symbol_assoc_get (x: symbol_t): int
  = "atsyacc_symbol_assoc_get"
fun symbol_assoc_set (x: symbol_t, assoc: int): void
  = "atsyacc_symbol_assoc_set"

(* ****** ****** *)

abstype symbolset_t // a boxed type for sets of symbols

val symbolset_nil : symbolset_t

fun symbolset_sing (x: symbol_t): symbolset_t

fun symbolset_is_nil (xs: symbolset_t): bool
fun symbolset_isnot_nil (xs: symbolset_t): bool

fun symbolset_ismem (xs: symbolset_t, x: symbol_t): bool

fun symbolset_add (xs: symbolset_t, x: symbol_t): symbolset_t
fun symbolset_union (xs: symbolset_t, ys: symbolset_t): symbolset_t

fun symbolset_add_flag (xs: symbolset_t, x: symbol_t, flag: &int): symbolset_t
fun symbolset_union_flag (xs: symbolset_t, ys: symbolset_t, flag: &int): symbolset_t

//

fun fprint_symbolset {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, _: symbolset_t): void

fun print_symbolset (_: symbolset_t): void
fun prerr_symbolset (_: symbolset_t): void

//

fun symbol_nullable_get (x: symbol_t): bool
  = "atsyacc_symbol_nullable_get"
fun symbol_nullable_set (x: symbol_t, nullable: bool): void
  = "atsyacc_symbol_nullable_set"

fun symbol_frstset_get (x: symbol_t): symbolset_t
  = "atsyacc_symbol_frstset_get"
fun symbol_frstset_set (x: symbol_t, frstset: symbolset_t): void
  = "atsyacc_symbol_frstset_set"

fun symbol_fllwset_get (x: symbol_t): symbolset_t
  = "atsyacc_symbol_fllwset_get"
fun symbol_fllwset_set (x: symbol_t, fllwset: symbolset_t): void
  = "atsyacc_symbol_fllwset_set"

(* ****** ****** *)

fun symbol_total_get (): int
fun symbol_term_total_get (): int
fun symbol_nonterm_total_get (): int

(* ****** ****** *)

(* end of [symbol.sats] *)
