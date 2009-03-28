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
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
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

#include "libc/CATS/string.cats"

%}

(* ****** ****** *)

symintr strcmp substrcmp

fun strcmp_string_string
  (str1: string, str2: string): int
  = "atslib_strcmp"

overload strcmp with strcmp_string_string
  
fun substrcmp_string_string
  {n1,i1:nat | i1 <= n1} {n2,i2:nat | i2 <= n2}
  (str1: string n1, i: size_t i1, str2: string n2, i2: size_t i2): int
  = "atslib_substrcmp"

overload substrcmp with substrcmp_string_string

//

fun strncmp_string_string {n:nat}
  (str1: string, str2: string, n: size_t n): int
  = "atslib_strncmp"

symintr strncmp substrncmp

overload strncmp with strncmp_string_string

fun substrncmp_string_string
  {n1,i1:nat | i1 <= n1} {n2,i2:nat | i2 <= n2} {n: nat} (
    str1: string n1, i1: size_t i1, str2: string n2, i2: size_t i2, n: size_t n
  ) : int
  = "atslib_substrncmp"

overload substrncmp with substrncmp_string_string

(* ****** ****** *)

fun strlen_string {n:nat} (str: string n): size_t n = "atslib_strlen"

(* ****** ****** *)

symintr strspn strcspn

fun strspn_string_string {n:nat} (str: string n, cs: string): sizeLte n
  = "atslob_strspn"
overload strspn with strspn_string_string

fun strcspn_string_string {n:nat} (str: string n, cs: string): sizeLte n
  = "atslob_strcspn"
overload strcspn with strcspn_string_string

(* ****** ****** *)

fun strcpy_strbuf_string
  {m,n:nat | n < m} {l:addr} {ofs:int} (
    pf_buf: !b0ytes m @ l >> strbuf (m, n) @ l | sbf: ptr l, str: string n
  ) : ptr l
  = "atslib_strcpy"

fun strcpy_strbuf_strbuf
  {m1,m2,n:nat | n < m1} {l:addr} {ofs:int} (
    pf_buf: !b0ytes m1 @ l >> strbuf (m1, n) @ l | dst: ptr l, src: &strbuf (m2, n)
  ) : ptr l
  = "atslib_strcpy"

(* ****** ****** *)

fun strcat_strbuf_string
  {m,n1,n2:nat | n1 + n2 < m} {l:addr} {ofs:int} (
    pf_mul: MUL (n1, sizeof char, ofs)
  , pf_buf: !strbuf (m, n1) @ l >> strbuf (m, n1+n2) @ l
  | sbf: ptr l, str: string n2
  ) : ptr l
  = "atslib_strcat"

(* ****** ****** *)

fun memcpy {n1,n2:nat}
  {n:nat | n <= n1; n <= n2} {l:addr} (
    pf_dst: !b0ytes n1 @ l >> bytes n1 @ l
  | dst: ptr l, src: &bytes n2, n: size_t n
  ) :<> ptr l
  = "atslib_memcpy"

(* ****** ****** *)

(* end of [string.sats] *)
