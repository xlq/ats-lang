(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
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

// October 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Fil = "ats_filename.sats"

(* ****** ****** *)

fun posmark_initiate (): void
fun posmark_terminate (): void

fun posmark_pause (): void
fun posmark_resume (): void

(* ****** ****** *)

typedef lint = int_long_t0ype

fun posmark_insert_comment_beg (li: lint): void
fun posmark_insert_comment_end (li: lint): void

fun posmark_insert_extern_beg (li: lint): void
fun posmark_insert_extern_end (li: lint): void

fun posmark_insert_keyword_beg (li: lint): void
fun posmark_insert_keyword_end (li: lint): void

fun posmark_insert_neuexp_beg (li: lint): void
fun posmark_insert_neuexp_end (li: lint): void

fun posmark_insert_staexp_beg (li: lint): void
fun posmark_insert_staexp_end (li: lint): void

fun posmark_insert_prfexp_beg (li: lint): void
fun posmark_insert_prfexp_end (li: lint): void

fun posmark_insert_dyncstdec_beg (li: lint): void
fun posmark_insert_dyncstdec_end (li: lint): void

fun posmark_insert_dyncstimp_beg (li: lint): void
fun posmark_insert_dyncstimp_end (li: lint): void

(* ****** ****** *)

fun posmark_file_make_tex (basename: string): void
fun posmark_file_make_htm (basename: string): void

(* ****** ****** *)

(* end of [ats_posmark.sats] *)

