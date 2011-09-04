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
// Start Time: September, 2011
//
(* ****** ****** *)

(*
** HX: help functions for writing xhtml documents via [atsdoc]
*)

(* ****** ****** *)

#ifndef ATSDOC_XHTMLATXT
#define ATSDOC_XHTMLATXT 1

(* ****** ****** *)
//
staload UN = "prelude/SATS/unsafe.sats"
//
staload
STDIO = "libc/SATS/stdio.sats"
staload TIME = "libc/SATS/time.sats"
//
dynload "libatsdoc/dynloadall.dats"
//
staload "libatsdoc/SATS/atsdoc_text.sats"
//
(* ****** ****** *)

val TEXTnewline = TEXTstrcst"\n"

(* ****** ****** *)

local
//
val LT = "<"
val LTSLASH = "</"
val GT = ">"
//
in

fun xmltagging (
  tag: string, x: string
) : text = let
  val _opn = TEXTappstr3 (LT, tag, GT)
  val _clo = TEXTappstr3 (LTSLASH, tag, GT)
in
  TEXTapptxt3 (_opn, TEXTstrsub(x), _clo)
end // end of [xmltagging]

end // end of [local]

(* ****** ****** *)

macdef head (x) = xmltagging ("head", ,(x))
macdef title (x) = xmltagging ("title", ,(x))
macdef body (x) = xmltagging ("body", ,(x))

(* ****** ****** *)

local
//
val COMMENTopn = TEXTstrcst"<!--"
and COMMENTcls = TEXTstrcst("-->")
//
in

fun comment (x: string): text =
  TEXTapptxt3 (COMMENTopn, TEXTstrsub(x), COMMENTcls)
// end of [comment]

end // end of [local]

(* ****** ****** *)

fun ignore (x: string): text = TEXTnil ()
fun ignoretxt (x: text): text = TEXTnil ()

(* ****** ****** *)

macdef strong(x) =
  xmltagging ("strong", ,(x)) // <strong> ... </strong>
// end of [strong]

(* ****** ****** *)

macdef textpre(x) = xmltagging ("pre", ,(x)) // <pre> ... </pre>

(* ****** ****** *)

fn pcenter
  (x: string): text = let
  val opn = TEXTstrcst"<p style=\"text-align: center;\">"
  val cls = TEXTstrcst"</p>"
in
  TEXTapptxt3 (opn, TEXTstrsub(x), cls)
end // end of [pcenter]

(* ****** ****** *)

fun timestamp
  (): text = let
  var time = $TIME.time_get ()
  val (fpf | x) = $TIME.ctime (time)
  val x1 = sprintf ("%s", @($UN.castvwtp1(x)))
  prval () = fpf (x)
  val x1 = string_of_strptr (x1)
in
  TEXTstrcst (x1)
end // end of [val]

(* ****** ****** *)

#endif // end of [#ifndef(ATSDOC_XHTMLATXT)

(* end of [xhtmlatxt.dats] *)
