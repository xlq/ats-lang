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
  (str1: string n1, i: int i1, str2: string n2, i2: int i2): int
  = "atslib_substrcmp"

overload substrcmp with substrcmp_string_string

//

fun strncmp_string_string {n:nat}
  (str1: string, str2: string, n: int n): int
  = "atslib_strncmp"

symintr strncmp substrncmp

overload strncmp with strncmp_string_string

fun substrncmp_string_string
  {n1,i1:nat | i1 <= n1} {n2,i2:nat | i2 <= n2} {n: nat} (
    str1: string n1, i1: int i1, str2: string n2, i2: int i2, n: int n
  ) : int
  = "atslib_substrncmp"

overload substrncmp with substrncmp_string_string

(* ****** ****** *)

(* end of [string.sats] *)
