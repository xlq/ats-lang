(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustworthy Software, Inc.
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
  | TEXTstrcst of string
  | TEXTstrsub of string
//
  | TEXTapptxt2 of (text, text)
  | TEXTappstr2 of (string, string)
//
  | TEXTapptxt3 of (text, text, text)
  | TEXTappstr3 of (string, string, string)
//
  | TEXTapptxt4 of (text, text, text, text)
  | TEXTappstr4 of (string, string, string, string)
//
  | TEXTnil of ()
//
  | TEXTcontxt of textlst
  | TEXTconstr of stringlst
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

fun fprint_text (out: FILEref, txt: text): void

(* ****** ****** *)

fun fprint_strsub (out: FILEref, str: string): void
fun fprint_filsub (out: FILEref, path: string): void

(* ****** ****** *)

(* end of [atsdoc_text.sats] *)
