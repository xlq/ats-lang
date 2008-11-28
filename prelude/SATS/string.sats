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

typedef bytes (sz:int) = @[byte][sz]

prval bytes_v_of_strbuf_v
  : {sz,n:nat} {l:addr} strbuf (sz, n) @ l -<prf> bytes (sz) @ l

(* ****** ****** *)

val string_empty : string 0

(* ****** ****** *)

fun string1_of_string0 (s: string):<> [n:nat] string n
  = "atspre_string1_of_string0"

fun string1_of_strbuf
  {m,n:nat} {l:addr} (pf: strbuf (m, n) @ l | p: ptr l):<> string n
  = "atspre_string1_of_strbuf"

fun strbuf_of_string1 {n:nat} (s: string n)
  :<> [m:nat | n < m] [l:addr] (vbox (strbuf (m, n) @ l) | ptr l)
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

//

fun compare_strbuf_strbuf {m1,n1,m2,n2:nat}
  (sb1: &strbuf (m1,n1), sb2: &strbuf (m2,n2)):<> Sgn
  = "atspre_compare_string_string"

fun compare_string_string (s1: string, s2: string):<> Sgn
  = "atspre_compare_string_string"

overload compare with compare_strbuf_strbuf
overload compare with compare_string_string

(* ****** ****** *)

fun fprint_strbuf {m,n:nat}
  (out: FILEref, x: &strbuf (m, n)):<!exnref> void
  = "atspre_fprint_string"

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

symintr strbuf_make
symintr string_make

(* ****** ****** *)

fun strbuf_make_char {n:nat}
  (n: int n, c: char):<> [l:addr] (strbuf (n+1, n) @ l | ptr l)
  = "atspre_strbuf_make_char"

fun string_make_char {n:nat} (n: int n, c: char):<> string n
  = "atspre_strbuf_make_char"

overload strbuf_make with strbuf_make_char
overload string_make with string_make_char

//

fun strbuf_make_list {n:nat}
  (cs: list (char, n)):<> [l:addr] (strbuf (n+1, n) @ l | ptr l)
  = "atspre_strbuf_make_list"

fun string_make_list {n:nat} (cs: list (char, n)):<> string n
  = "atspre_strbuf_make_list"

overload strbuf_make with strbuf_make_list
overload string_make with string_make_list

//

fun strbuf_make_list_len {n:nat}
  (cs: list (char, n), n: int n):<> [l:addr] (strbuf (n+1, n) @ l | ptr l)
  = "atspre_strbuf_make_list_len"

fun string_make_list_len {n:nat}
  (cs: list (char, n), n: int n):<> string n
  = "atspre_strbuf_make_list_len"

overload strbuf_make with strbuf_make_list_len
overload string_make with string_make_list_len

//

fun strbuf_make_bufptr
  {n,st,ln:nat | st + ln <= n} {l_buf:addr}
  (pf: !bytes n @ l_buf | p: ptr l_buf, st: int st, ln: int ln)
  :<> [l:addr] (strbuf (ln+1, ln) @ l | ptr l)
  = "atspre_strbuf_make_bufptr"

fun strbuf_make_substrbuf
  {m,n,st,ln:nat | st + ln <= n}
  (sb: &strbuf (m, n), st: int st, ln: int ln)
  :<> [l:addr] (strbuf (ln+1, ln) @ l | ptr l)
  = "atspre_strbuf_make_bufptr"

fun string_make_substring
  {n,st,ln:nat | st + ln <= n}
  (s: string n, st: int st, ln: int ln):<> string ln
  = "atspre_strbuf_make_bufptr"


overload strbuf_make with strbuf_make_bufptr
overload strbuf_make with strbuf_make_substrbuf
overload string_make with string_make_substring

(* ****** ****** *)

fun strbuf_append {m1,n1,m2,n2:nat | n1+n2 < m1}
  (sb1: &strbuf (m1,n1) >> strbuf (m1, n1+n2), sb2: &strbuf (m2,n2)):<> void
  = "atspre_strbuf_append"

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

fun string_concat (xs: List string):<> string

(* ****** ****** *)

fun strbuf_contains {m,n:nat} (sb: &strbuf (m, n), c: char):<> bool
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

fun strbuf_is_empty {m,n:nat} (sb: &strbuf (m, n)):<> bool (n==0)
  = "atspre_string_is_empty"
fun string0_is_empty (s: string):<> bool
  = "atspre_string_is_empty"
fun string1_is_empty {n:nat} (s: string n):<> bool (n==0)
  = "atspre_string_is_empty"

fun strbuf_is_not_empty {m,n:nat} (sb: &strbuf (m, n)):<> bool (n > 0)
  = "atspre_string_is_not_empty"

overload ~ with strbuf_is_not_empty

fun string0_is_not_empty (s: string):<> bool
  = "atspre_string_is_not_empty"
fun string1_is_not_empty {n:nat} (s: string n):<> bool (n > 0)
  = "atspre_string_is_not_empty"

overload ~ with string0_is_not_empty
overload ~ with string1_is_not_empty

(* ****** ****** *)

fun strbuf_is_at_end
  {m,n,i:nat | i <= n} (sb: &strbuf (m, n), i: int i):<> bool (i == n)
  = "atspre_string_is_at_end"

fun string1_is_at_end
  {n,i:nat | i <= n} (s: string n, i: int i):<> bool (i == n)
  = "atspre_string_is_at_end"

(* ****** ****** *)

// alias of [string_to_list]
fun strbuf_explode {m,n:nat} (sb: &strbuf (m, n)):<> list (char, n)

fun string0_explode (s: string):<> List char
  = "atspre_string_explode"

fun string1_explode {n:nat} (s: string n):<> list (char, n)
  = "atspre_string_explode"

(* ****** ****** *)

fun strbuf_get_char_at {m,n:nat}
  (sb: &strbuf (m, n), i: natLt n):<> char
  = "atspre_string_get_char_at"

fun string_get_char_at {n:nat} (s: string n, i: natLt n):<> char
  = "atspre_string_get_char_at"

overload [] with strbuf_get_char_at
overload [] with string_get_char_at

fun string_get_char_at_exn (s: string, i: Nat):<!exn> char

(* ****** ****** *)

fun strbuf_set_char_at {m,n:nat}
  (sb: &strbuf (m, n), i: natLt n, c: char):<> void
  = "atspre_strbuf_set_char_at"

fun string_set_char_at {n:nat}
  (s: string n, i: natLt n, c: char):<!ref> void
  = "atspre_strbuf_set_char_at"

overload [] with strbuf_set_char_at
overload [] with string_set_char_at

fun string_set_char_at_exn (s: string, i: Nat, c: char):<!exnref> void

(* ****** ****** *)

// alias of [string_make_list]
fun string_implode {n:nat} (cs: list (char, n)):<> string n
  = "atspre_string_implode"

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

fun strbuf_index_of_char_from_right // locate a character from left
  {m,n:nat} (sb: &strbuf (m, n), c: char):<> [i:int | ~1 <= i; i <= n] int i
  = "atspre_string_index_of_char_from_right"

fun string_index_of_char_from_right // locate a character from left
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

fun strbuf_tolower {m,n:nat} (sb: &strbuf (m, n)):<> void
  = "atspre_string_tolower"
fun string0_tolower (s: string):<> string
  = "atspre_string_tolower"
fun string1_tolower {n:nat} (s: string n):<> string n
  = "atspre_string_tolower"

symintr string_tolower

overload string_tolower with string0_tolower
overload string_tolower with string1_tolower

(* ****** ****** *)

fun strbuf_toupper {m,n:nat} (sb: &strbuf (m, n)):<> void
  = "atspre_string_toupper"
fun string0_toupper (s: string):<> string
  = "atspre_string_toupper"
fun string1_toupper {n:nat} (s: string n):<> string n
  = "atspre_string_toupper"

symintr string_toupper

overload string_toupper with string0_toupper
overload string_toupper with string1_toupper

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
