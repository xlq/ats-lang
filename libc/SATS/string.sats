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
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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

#include "libc/CATS/string.cats"

%}

(* ****** ****** *)

fun strcmp (str1: string, str2: string): int = "atslib_strcmp"

fun substrcmp
  {n1,i1:nat | i1 <= n1} {n2,i2:nat | i2 <= n2}
  (str1: string n1, i: size_t i1, str2: string n2, i2: size_t i2): int
  = "atslib_substrcmp"

(* ****** ****** *)

fun strncmp {n:nat}
  (str1: string, str2: string, n: size_t n):<> int
  = "atslib_strncmp"

fun substrncmp
  {n1,i1:nat | i1 <= n1} {n2,i2:nat | i2 <= n2} {n: nat} (
    str1: string n1, i1: size_t i1, str2: string n2, i2: size_t i2, n: size_t n
  ) :<> int
  = "atslib_substrncmp"

(* ****** ****** *)

fun strlen {n:nat} (str: string n):<> size_t n = "atslib_strlen"

(* ****** ****** *)

(*

char *strchr(const char *, int):
please use [string_index_of_char_from_left] in [prelude/SATS/string.sats]

char *strrchr(const char *, int):
please use [string_index_of_char_from_right] in [prelude/SATS/string.sats]

*)

(* ****** ****** *)

fun strspn {n:nat} (str: string n, accept: string):<> sizeLte n
  = "atslob_strspn"

fun strcspn {n:nat} (str: string n, reject: string):<> sizeLte n
  = "atslob_strcspn"

(* ****** ****** *)

fun strcpy
  {m,n:nat | n < m} {l:addr} {ofs:int} (
    pf_buf: !b0ytes m @ l >> strbuf (m, n) @ l | sbf: ptr l, str: string n
  ) :<> ptr l
  = "atslib_strcpy"

(* ****** ****** *)

fun strcat
  {m,n1,n2:nat | n1 + n2 < m} {l:addr} {ofs:int} (
    pf_mul: MUL (n1, sizeof char, ofs)
  , pf_buf: !strbuf (m, n1) @ l >> strbuf (m, n1+n2) @ l
  | sbf: ptr l, str: string n2
  ) :<> ptr l
  = "atslib_strcat"

(*

char *strncat(char *dst, const char *src, size_t n):
note that there is really no need for this function given that [strcat] is safe!

*)

(* ****** ****** *)

(*

char *strpbrk(const char *str, const char *accept);

*)

dataprop strpbrk_p (l:addr, n:int, l_ret:addr) =
  | {i:nat | i < n} {l_ret == l+i} strpbrk_p_some (l, n, l_ret)
  | {l_ret == null} strpbrk_p_none (l, n, l_ret)

fun strpbrk {m,n:nat} {l:addr}
  (pf: !strbuf (m, n) @ l | p: ptr l, accept: string)
  :<> [l_ret:addr] (strpbrk_p (l, n, l_ret) | ptr l_ret)
  = "atslib_strpbrk"

(* ****** ****** *)

// implemented in [string.dats]
fun strdup_gc {n:nat} (str: string n)
  :<> [l:addr] (free_gc_v (n+1, l), strbuf (n+1, n) @ l | ptr l)

fun strdup_ngc {n:nat} (str: string n)
  :<> [l:addr] (free_ngc_v (n+1, l), strbuf (n+1, n) @ l | ptr l)

(* ****** ****** *)

fun memcmp {n:nat}
  {n1,n2:nat | n <= n1; n <= n2} (
    buf1: &bytes n1, buf2: &bytes n2, n: size_t n
  ) :<> int
  = "atslib_memcmp"

(* ****** ****** *)

fun memcpy {n:nat}
  {n1,n2:nat | n <= n1; n <= n2} {l:addr} (
    pf_dst: !bytes n1 @ l | p_dst: ptr l, p_src: &bytes n2, n: size_t n
  ) :<> ptr l
  = "atslib_memcpy"

(* ****** ****** *)

fun memset {n:nat}
  {n1:nat | n <= n1} {l:addr} (
    pf: !bytes n1 @ l | p: ptr l, chr: int, n: size_t n
  ) :<> ptr l
  = "atslib_memset"

(* ****** ****** *)

dataprop memchr_p (l:addr, n:int, l_ret:addr) =
  | {i:nat | i < n} {l_ret == l+i} memchr_p_some (l, n, l_ret)
  | {l_ret == null} memchr_p_none (l, n, l_ret)

fun memchr {n:nat}
  {n1:nat | n <= n1} {l:addr} (
    pf: !bytes n1 @ l | p: ptr l, chr: int, n: size_t n
  ) : [l_ret:addr] (memchr_p (l, n, l_ret) | ptr l_ret)
  = "atslib_memchr"

(* ****** ****** *)

(* end of [string.sats] *)

////
                  
void    *memccpy(void *dst, const void *src, int/*c*/, size_t n);
void    *memmove(void *, const void *, size_t);
char    *strerror(int);
int     *strerror_r(int, char *, size_t);
