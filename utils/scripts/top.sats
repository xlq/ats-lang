(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
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

// Time: Summer 2007

(* Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

val ATSHOME_dir : String = "ATSHOME_dir"

val atsopt_local : String = "atsopt_local"
and atsopt_global : String = "atsopt_global"

val precats_local : String = "precats_local"
and precats_global : String = "precats_global"

val runtime_local : String = "runtime_local"
and runtime_global : String = "runtime_global"

val atslib_local : String = "atslib_local"
and atslib_global : String = "atslib_global"

val atslib_output_local : String = "atslib_output_local"
and atslib_output_global : String = "atslib_output_global"

val libats_local : String = "libats_local"
and libats_global : String = "libats_global"

val libats_mt_local : String = "libats_mt_local"
and libats_mt_global : String = "libats_mt_global"

(* ****** ****** *)

fun ATSHOME_dir_append (s: string): String
fun basename_of_filename (s: string): String
fun suffix_of_filename (s: string): Stropt
fun filename_is_local (s: string): Bool

(* ****** ****** *)

fun file_is_exec (file: string) : Bool = "file_is_exec"
fun getcwd () : String = "__ats_getcwd"

(* ****** ****** *)

abstype intref // boxed type = ats_intref_type

fun intref_make (i: int): intref = "intref_make"
fun intref_get (r: intref): int = "intref_get"
fun intref_set (r: intref, i: int): void = "intref_set"

(* ****** ****** *)

datatype strlst (int) =
  | STRLSTnil (0) | {n:nat} STRLSTcons (n+1) of (string, strlst n)

typedef Strlst = [n:nat] strlst n

fun strlst_nil (): strlst 0 = "strlst_nil"
fun strlst_is_nil {n:nat} (ss: strlst n): bool (n == 0) = "strlst_is_nil"
fun strlst_head_get {n:pos} (ss: strlst n): string = "strlst_head_get"
fun strlst_tail_get {n:pos} (ss: strlst n): strlst (n-1) = "strlst_tail_get"

fun strlst_length {n:nat} (ss: strlst n): size_t n = "strlst_length"
fun strlst_reverse {n:nat} (ss: strlst n): strlst n = "strlst_reverse"

(* ****** ****** *)

fun strlst_to_strarr {n:nat} {l:addr}
  (pf: !array_v (String?, n, l) >> array_v (String, n, l) | ss: strlst n, p: ptr l)
  : void
  = "strlst_to_strarr"

fun string_trans (s: string, f: char -<cloptr1> String): String
  = "string_trans"

(* ****** ****** *)

fun ccomp_file_to_file_err
  (flag_stadyn: int, param_ats: Strlst, infile: string, outfile: string): int

fun ccomp_file_to_file
  (flag_stadyn: int, param_ats: Strlst, infile: string, outfile: string): void

fun typecheck_file
  (flag_stadyn: int, param_ats: Strlst, infile: string): void

fun atscc_version (): void

(* ****** ****** *)

fun gcc_libfile_err (infile: string, outfile: string): int
fun ar_r_err (libfile: string, objfile: string): int

fun ccomp_gcc_ar_libfile (infile: string, libfile: string): void

fun libats_make (): void
fun libats_mt_make (): void
fun libatslex_make (): void

(* ****** ****** *)

(* end of top.sats *)
