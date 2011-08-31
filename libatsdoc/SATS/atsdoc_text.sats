(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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
//
// Author: Hongwei Xi (gmhwxi AT gmail DOT com)
// Start Time: July, 2011
//
(* ****** ****** *)

staload
SYM = "libatsdoc/SATS/atsdoc_symbol.sats"
typedef symbol = $SYM.symbol

(* ****** ****** *)

datatype text =
//
  | TEXTstrcst of string // string constants
  | TEXTstrsub of string // strings containing marked tokens
//
  | TEXTapptxt2 of (text, text) // text concatenation
  | TEXTappstr2 of (string, string) // string concatenation
//
  | TEXTapptxt3 of (text, text, text) // text concatenation
  | TEXTappstr3 of (string, string, string) // string concatenation
//
  | TEXTapptxt4 of (text, text, text, text) // text concatenation
  | TEXTappstr4 of (string, string, string, string) // string concatenation
//
  | TEXTnil of () // empty text
//
  | TEXTcontxt of textlst // text concatenation
  | TEXTcontxtsep of (textlst, text(*sep*)) // text concatenation with separator
// end of [text]

where
textlst = List (text)
and
stringlst = List (string)

(* ****** ****** *)

fun atscode2xml_strcode (stadyn: int, code: string): text
fun atscode2xml_filcode (stadyn: int, path: string): text

(* ****** ****** *)

fun theTextMap_search (s: symbol): Option_vt (text)
fun theTextMap_insert (s: symbol, txt: text): void
fun theTextMap_insert_str (s: string, txt: text): void

(* ****** ****** *)

fun fprint_text (out: FILEref, x: text): void
fun fprint_textlst (out: FILEref, xs: textlst): void
fun fprint_textlst_sep (out: FILEref, xs: textlst, sep: text): void

(* ****** ****** *)

fun fprint_strsub (out: FILEref, sub: string): void
fun fprint_filsub (out: FILEref, path: string): void

(* ****** ****** *)
//
// HX: this one is generic and should probably be moved into libats
//
fun{a:t@ype}
tostring_fprint
  (prfx: string, fpr: (FILEref, a) -> void, x: a): strptr0
// end of [tostring_fprint]

fun tostring_strsub (sub: string): strptr0

(* ****** ****** *)

(* end of [atsdoc_text.sats] *)
