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

// some string operations

#if VERBOSE_PRELUDE #then

#print "Loading [string.sats] starts!\n"

#endif

(* ****** ****** *)

stadef NUL = '\000'

(* ****** ****** *)

typedef bytes (n:int) = @[byte][n]
typedef b0ytes (n:int) = @[byte?][n]

typedef chars (n:int) = @[char][n]
typedef c0hars (n:int) = @[char?][n]
typedef c1har = [c:char | c <> NUL] char c
typedef c1hars (n:int) = @[c1har][n]

(* ****** ****** *)

praxi bytes_v_of_b0ytes_v {bsz:int}
  {l:addr} (pf: b0ytes (bsz) @ l):<prf> bytes (bsz) @ l

praxi char_v_of_b0yte_v {l:addr} (pf: byte? @ l): char @ l

praxi chars_v_of_b0ytes_v {bsz:int}
  {l:addr} (pf: b0ytes (bsz) @ l):<prf> chars (bsz) @ l

(* ****** ****** *)

praxi bytes_v_of_chars_v {bsz:int}
  {l:addr} (pf: chars (bsz) @ l):<prf> bytes (bsz) @ l

praxi bytes_v_of_strbuf_v {bsz:int}
  {l:addr} (pf: strbuf (bsz) @ l):<prf> bytes (bsz) @ l

(* ****** ****** *)

viewdef strbuf_v (m: int, n: int, l:addr) = strbuf (m, n) @ l

praxi strbuf_v_null {n:nat} {l:addr}
  (pf1: char NUL @ l, pf2: b0ytes (n) @ l + sizeof(char))
  : strbuf_v (n+1, 0, l)

//

praxi strbuf_v_cons
  {m,n:nat} {l:addr}
  (pf1: c1har @ l, pf2: strbuf_v (m, n, l + sizeof(char)))
  :<prf> strbuf_v (m+1, n+1, l)

//

dataview strbufopt_v (int, int, addr, char) =
  | {m:nat} {l:addr}
    strbufopt_v_none (m, ~1, l, NUL) of b0ytes m @ l
  | {m,n:nat} {l:addr} {c:char | c <> NUL}
    strbufopt_v_some (m, n, l, c) of strbuf_v (m, n, l)

praxi strbuf_v_uncons
  {m,n:nat} {l:addr} (pf: strbuf_v (m, n, l))
  :<prf> [c:char] @(
     char c @ l, strbufopt_v (m-1, n-1, l + sizeof(char), c)
   )

//

prfun strbuf_v_split
  {m,n:nat} {i:nat | i <= n} {l:addr} {ofs:int}
  (pf_mul: MUL (i, sizeof char, ofs), pf_str: strbuf_v (m, n, l))
  : (c1hars i @ l, strbuf_v (m-i, n-i, l+ofs))

prfun strbuf_v_unsplit
  {n1:nat} {m2,n2:nat} {l:addr} {ofs:int} (
    pf_mul: MUL (n1, sizeof char, ofs)
  , pf_buf: c1hars n1 @ l
  , pf_str: strbuf_v (m2, n2, l+ofs)
  ) : strbuf_v (n1+m2, n1+n2, l)

(* ****** ****** *)

fun bytes_strbuf_trans {m,n:nat | n < m} {l:addr}
  (pf: !b0ytes m @ l >> strbuf (m, n1) @ l | p: ptr l, n: int n)
  :<> #[n1: nat | n1 <= n] void
  = "atspre_bytes_strbuf_trans"

(* ****** ****** *)

val string_empty : string 0

(* ****** ****** *)

fun string1_of_string (s: string):<> [n:nat] string n
  = "atspre_string1_of_string"

fun string1_of_strbuf {m,n:nat} {l:addr}
  (pf: strbuf (m, n) @ l | p: ptr l) :<> string n
  = "atspre_string1_of_strbuf"

fun strbuf_of_string1 {n:nat} (s: string n)
  :<> [m:int | n < m] [l:addr] (vbox (strbuf (m, n) @ l) | ptr l)
  = "atspre_strbuf_of_string1"

(* ****** ****** *)

fun lt_strbuf_strbuf {m1,n1,m2,n2:nat}
   (sb1: &strbuf (m1,n1), sb2: &strbuf (m2,n2)):<> bool
  = "atspre_lt_string_string"

fun lt_string_string (s1: string, s2: string):<> bool
  = "atspre_lt_string_string"

overload < with lt_strbuf_strbuf
overload < with lt_string_string

//

fun lte_strbuf_strbuf {m1,n1,m2,n2:nat}
  (sb1: &strbuf (m1,n1), sb2: &strbuf (m2,n2)):<> bool
  = "atspre_lte_string_string"

fun lte_string_string (s1: string, s2: string):<> bool
  = "atspre_lte_string_string"

overload <= with lte_strbuf_strbuf
overload <= with lte_string_string

//

fun gt_strbuf_strbuf {m1,n1,m2,n2:nat}
   (sb1: &strbuf (m1,n1), sb2: &strbuf (m2,n2)):<> bool
  = "atspre_gt_string_string"

fun gt_string_string (s1: string, s2: string):<> bool
  = "atspre_gt_string_string"

overload > with gt_strbuf_strbuf
overload > with gt_string_string

//

fun gte_strbuf_strbuf {m1,n1,m2,n2:nat}
  (sb1: &strbuf (m1,n1), sb2: &strbuf (m2,n2)):<> bool
  = "atspre_gte_string_string"

fun gte_string_string (s1: string, s2: string):<> bool
  = "atspre_gte_string_string"

overload >= with gte_strbuf_strbuf
overload >= with gte_string_string

//

fun eq_strbuf_strbuf {m1,n1,m2,n2:nat}
  (sb1: &strbuf (m1,n1), sb2: &strbuf (m2,n2)):<> bool
  = "atspre_eq_string_string"

fun eq_string_string (s1: string, s2: string):<> bool
  = "atspre_eq_string_string"

overload = with eq_strbuf_strbuf
overload = with eq_string_string

//

fun neq_strbuf_strbuf {m1,n1,m2,n2:nat}
  (sb1: &strbuf (m1,n1), sb2: &strbuf (m2,n2)):<> bool
  = "atspre_neq_string_string"

fun neq_string_string (s1: string, s2: string):<> bool
  = "atspre_neq_string_string"

overload <> with neq_strbuf_strbuf
overload <> with neq_string_string

(* ****** ****** *)

fun compare_strbuf_strbuf {m1,n1,m2,n2:nat}
  (sb1: &strbuf (m1,n1), sb2: &strbuf (m2,n2)):<> Sgn
  = "atspre_compare_string_string"

fun compare_strbuf_string {m1,n1:nat}
  (sb1: &strbuf (m1,n1), sb2: string):<> Sgn
  = "atspre_compare_string_string"

fun compare_strbuf_string {m2,n2:nat}
  (sb1: string, sb2: &strbuf (m2,n2)):<> Sgn
  = "atspre_compare_string_string"

fun compare_string_string (s1: string, s2: string):<> Sgn
  = "atspre_compare_string_string"

overload compare with compare_strbuf_strbuf
overload compare with compare_string_string

(* ****** ****** *)

fun fprint_strbuf {m,n:int}
  (out: FILEref, x: &strbuf (m, n)):<!exnref> void
  = "atspre_fprint_string"

fun print_strbuf {m,n:int} (x: &strbuf (m, n)):<!ref> void
  = "atspre_print_string"
and prerr_strbuf {m,n:int} (x: &strbuf (m, n)):<!ref> void
  = "atspre_prerr_string"

overload print with print_strbuf
overload prerr with prerr_strbuf

(* ****** ****** *)

symintr fprint_string

fun fprint0_string (out: FILEref, x: string):<!exnref> void
  = "atspre_fprint_string"

fun fprint1_string {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: string):<!exnref> void
  = "atspre_fprint_string"

overload fprint_string with fprint0_string
overload fprint_string with fprint1_string
overload fprint with fprint_string

(* ****** ****** *)

fun print_string (b: string):<!ref> void = "atspre_print_string"
and prerr_string (b: string):<!ref> void = "atspre_prerr_string"

overload print with print_string
overload prerr with prerr_string

(* ****** ****** *)

fun strbuf_initialize_substring {bsz:int} {n:int}
  {st,ln:nat | st+ln <= n; ln < bsz} {l:addr} (
    pf: !b0ytes bsz @ l >> strbuf (bsz, ln) @ l
  | p: ptr l, s: string n, st: int st, ln: int ln
  ) : void
  = "atspre_strbuf_initialize_substring"

(* ****** ****** *)

fun string_make_char {n:nat} (n: int n, c: char):<> string n
  = "atspre_string_make_char"

fun string_make_list {n:nat} (cs: list (char, n)):<> string n
  = "atspre_string_make_list"

fun string_make_list_len {n:nat}
  (cs: list (char, n), n: int n):<> string n
  = "atspre_string_make_list_len"

fun string_make_substring
  {n:int} {st,ln:nat | st + ln <= n}
  (s: string n, st: int st, ln: int ln):<> string ln
  = "atspre_string_make_substring"

fun string_make_substrbuf
  {m,n:int} {st,ln:nat | st + ln <= n}
  (s: &strbuf (m, n), st: int st, ln: int ln):<> string ln
  = "atspre_string_make_substring"

(* ****** ****** *)

fun string0_append (s1: string, s2: string):<> string
  = "atspre_string_append" 

fun string1_append {i,j:nat} (s1: string i, s2: string j):<> string (i+j)
  = "atspre_string_append"

overload + with string0_append
overload + with string1_append

(* ****** ****** *)

fun string_compare (s1: string, s2: string):<> Sgn
  = "atspre_compare_string_string"

(* ****** ****** *)

fun stringlst_concat (xs: List string):<> string

(* ****** ****** *)

fun strbuf_contains {m,n:nat}
  (sb: &strbuf (m, n), c: char):<> bool
  = "atspre_string_contains"

fun string_contains (s: string, c: char):<> bool
  = "atspre_string_contains"

(* ****** ****** *)

fun string_equal (s1: string, s2: string):<> bool
  = "atspre_eq_string_string"

(* ****** ****** *)

fun strbuf_length {m,n:nat} (sb: &strbuf (m, n)):<> int n
  = "atspre_string_length"

overload length with strbuf_length

fun string0_length (s: string):<> Nat
  = "atspre_string_length"

fun string1_length {n:nat} (s: string n):<> int n
  = "atspre_string_length"

symintr string_length
overload string_length with string0_length
overload string_length with string1_length

overload length with string_length

(* ****** ****** *)

symintr string_is_empty

fun strbuf_is_empty {m,n:nat}
  (sb: &strbuf (m, n)):<> bool (n==0)
  = "atspre_string_is_empty"

fun string0_is_empty (s: string):<> bool
  = "atspre_string_is_empty"

fun string1_is_empty {n:nat} (s: string n):<> bool (n==0)
  = "atspre_string_is_empty"

overload string_is_empty with string0_is_empty
overload string_is_empty with string1_is_empty

(* ****** ****** *)

symintr string_isnot_empty

fun strbuf_isnot_empty {m,n:nat}
  (sb: &strbuf (m, n)):<> bool (n > 0)
  = "atspre_string_isnot_empty"

fun string0_isnot_empty (s: string):<> bool
  = "atspre_string_isnot_empty"

fun string1_isnot_empty {n:nat} (s: string n):<> bool (n > 0)
  = "atspre_string_isnot_empty"

overload string_isnot_empty with string0_isnot_empty
overload string_isnot_empty with string1_isnot_empty

(* ****** ****** *)

fun strbuf_is_at_end
  {m,n,i:nat | i <= n} (sb: &strbuf (m, n), i: int i):<> bool (i == n)
  = "atspre_string_is_at_end"

fun string_is_at_end
  {n,i:nat | i <= n} (s: string n, i: int i):<> bool (i == n)
  = "atspre_string_is_at_end"

(* ****** ****** *)

// alias of [string_to_list]
fun strbuf_explode {m,n:nat} (sb: &strbuf (m, n)):<> list_vt (char, n)
  = "atspre_string_explode"

fun string_explode {n:nat} (s: string n):<> list_vt (char, n)
  = "atspre_string_explode"

(* ****** ****** *)

fun strbuf_get_char_at {m,n:nat}
  (sb: &strbuf (m, n), i: natLt n):<> [c:char | c <> NUL] char c
  = "atspre_string_get_char_at"

fun string_get_char_at {n:nat}
  (s: string n, i: natLt n):<!ref> [c:char | c <> NUL] char c
  = "atspre_string_get_char_at"

overload [] with strbuf_get_char_at
overload [] with string_get_char_at

(* ****** ****** *)

fun strbuf_set_char_at {m,n:nat} {c: char | c <> NUL}
  (sb: &strbuf (m, n), i: natLt n, c: char c):<> void
  = "atspre_strbuf_set_char_at"

fun string_set_char_at {n:nat} {c:char | c <> NUL}
  (s: string n, i: natLt n, c: char c):<!ref> void
  = "atspre_strbuf_set_char_at"

overload [] with strbuf_set_char_at
overload [] with string_set_char_at

(* ****** ****** *)

// alias of [string_make_list]
fun string_implode {n:nat} (cs: list (char, n)):<> string n
  = "atspre_string_make_list"

(* ****** ****** *)

// This function is based on [strchr] in [string.h]
// the NULL character at the end of a string is considered in the string

fun strbuf_index_of_char_from_left // locate a character from left
  {m,n:nat} (sb: &strbuf (m,n), c: char):<> [i:int | ~1 <= i; i <= n] int i
  = "atspre_string_index_of_char_from_left"

fun string_index_of_char_from_left // locate a character from left
  {n:nat} (s: string n, c: char):<> [i:int | ~1 <= i; i <= n] int i
  = "atspre_string_index_of_char_from_left"

// This function is based on [strrchr] in [string.h]
// the NULL character at the end of a string is considered in the string

fun strbuf_index_of_char_from_right // locate a character from right
  {m,n:nat} (sb: &strbuf (m, n), c: char):<> [i:int | ~1 <= i; i <= n] int i
  = "atspre_string_index_of_char_from_right"

fun string_index_of_char_from_right // locate a character from right
  {n:nat} (s: string n, c: char):<> [i:int | ~1 <= i; i <= n] int i
  = "atspre_string_index_of_char_from_right"

(* ****** ****** *)

// This function is based on [strstr] in [string.h]
// Note that the NULL character is not compared
fun string_index_of_string // locate a substring from left
  {n1,n2:nat} (s1: string n1, s2: string n2):<> [i:int | ~1 <= i; i < n1] int i
  = "atspre_string_index_of_string"

(* ****** ****** *)

fun string_singleton (c: char):<> string 1

(* ****** ****** *)

// implemented in [prelude/DATS/string.dats]
// a new string is created
fun string_tolower {n:nat} (s: string n):<> string n
  = "atspre_string_tolower"

// implemented in [prelude/DATS/string.dats]
// a new string is created
fun string_toupper {n:nat} (s: string n):<> string n
  = "atspre_string_toupper"

(* ****** ****** *)

// h = (h << 5) + h + c
fun string_hash_33 (s: string):<> uInt = "atspre_string_hash_33"

(* ****** ****** *)

// functions for optional strings

val stropt_none : stropt (~1)
  = "atspre_stropt_none"
fun stropt_some {n:nat} (s: string n):<> stropt n
  = "atspre_stropt_some"
fun stropt_unsome {n:nat} (s: stropt n):<> string n
  = "atspre_stropt_unsome"

fun stropt_is_none {i:int} (s: stropt i):<> bool (i < 0)
  = "atspre_stropt_is_none"
fun stropt_is_some {i:int} (s: stropt i):<> bool (i >= 0)
  = "atspre_stropt_is_some"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [string.sats] finishes!\n"

#endif

(* end of [string.sats] *)
