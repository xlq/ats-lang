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
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#

#include "libats/CATS/regexp.cats"

%}

(* ****** ****** *)

abst@ype REGEXP
abstype REGEXPref

(* ****** ****** *)

fun regexp_compile_exn (pattern: string)
  : [l:addr] (free_gc_v l, REGEXP @ l | ptr l)
  = "atslib_regexp_compile_exn"

fun regexp_free {l:addr}
  (pf_gc: free_gc_v l, pf_at: REGEXP @ l | p: ptr l): void
  = "atslib_regexp_free"

(* ****** ****** *)

fun regexp_ref_make {l:addr}
  (pf_gc: free_gc_v l, pf_at: REGEXP @ l | p: ptr l): REGEXPref
  = "atslib_regexp_ref_make"

(* ****** ****** *)

fun test_regexp_match_str (re: &REGEXP, str: string): bool

fun test_regexp_match_str_len_ofs
  {n,i:int | 0 <= i; i <= n }
  (re: &REGEXP, str: string n, len: int n, ofs: int i): bool
  = "atslib_test_regexp_match_str_len_ofs"

symintr test_regexp_match
overload test_regexp_match with test_regexp_match_str
overload test_regexp_match with test_regexp_match_str_len_ofs

(* ****** ****** *)

fun string_split_regexp (str: string, re: REGEXPref): stream string
  = "atslib_string_split_regexp"

(* ****** ****** *)

(* end of [regexp.sats] *)
