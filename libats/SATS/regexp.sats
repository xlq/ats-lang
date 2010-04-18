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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "libats/CATS/regexp.cats"
%} // end of [%{#]

(* ****** ****** *)

absviewtype REGEXPptr (l:addr)
viewtypedef REGEXPptr0 = [l:agez] REGEXPptr l
viewtypedef REGEXPptr1 = [l:addr | l > null] REGEXPptr l
//
castfn ptr_of_REGEXPptr {l:addr} (x: !REGEXPptr l): ptr l
overload ptr_of with ptr_of_REGEXPptr
//
abstype REGEXPref // = ref (REGEXP)

(* ****** ****** *)

// implemented in C
fun regexp_compile (pattern: string): REGEXPptr0
  = "atslib_regexp_compile"
// end of [regexp_compile]

// implemented in ATS
fun regexp_compile_exn (pattern: string): REGEXPptr1

(* ****** ****** *)

castfn regexp_free_null (p: REGEXPptr null): ptr(*null*)

fun regexp_free
  {l:agz} (p: REGEXPptr l): void = "atslib_regexp_free"
// end of [regexp_free]

(* ****** ****** *)

fun regexp_ref_make {l:agz} (p: REGEXPptr l): REGEXPref

(* ****** ****** *)

fun test_regexp_match_str {l:agz}
  (re: !REGEXPptr l, str: string): bool

fun test_regexp_match_str_len_ofs
  {l:agz} {n,i:int | 0 <= i; i <= n }
  (re: !REGEXPptr l, str: string n, len: int n, ofs: int i): bool
  = "atslib_test_regexp_match_str_len_ofs"
// end of [test_regexp_match_str_len_ofs]

symintr test_regexp_match
overload test_regexp_match with test_regexp_match_str
overload test_regexp_match with test_regexp_match_str_len_ofs

(* ****** ****** *)

fun string_split_regexp
  (str: string, re: REGEXPref): stream string
  = "atslib_string_split_regexp"
// end of [string_split_regexp]

(* ****** ****** *)

(* end of [regexp.sats] *)
