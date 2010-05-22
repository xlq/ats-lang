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
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: May, 2010

(* ****** ****** *)

typedef PangoColor =
  $extype_struct "PangoColor" of {
  red= guint16
, green= guint16
, blue= guint16
} // end of [PangoColor]

(* ****** ****** *)

fun pango_color_copy
  (src: &PangoColor)
  : [l:addr] (PangoColor @ l | ptr l) = "#atsctrb_pango_color_copy"
// end of [pango_color_copy]

fun pango_color_free {l:addr} (
    pf1: PangoFree_v l, pf2: PangoColor @ l | p: ptr l
  ) : void = "#atsctrb_pango_color_free"
// end of [pango_color_free]

fun pango_color_parse {l:agz} (
    clr: &PangoColor? >> opt (PangoColor, b), spec: !gstring l
  ) : #[b: bool] gboolean b = "#atsctrb_pango_color_parse"
// end of [pango_color_parse]

(* ****** ****** *)

abst@ype PangoAttrType = $extype "PangoAttrType"
macdef PANGO_ATTR_INVALID = $extval (PangoAttrType, "PANGO_ATTR_INVALID")
macdef PANGO_ATTR_LANGUAGE = $extval (PangoAttrType, "PANGO_ATTR_LANGUAGE")
macdef PANGO_ATTR_FAMILY = $extval (PangoAttrType, "PANGO_ATTR_FAMILY")
macdef PANGO_ATTR_STYLE = $extval (PangoAttrType, "PANGO_ATTR_STYLE")
macdef PANGO_ATTR_WEIGHT = $extval (PangoAttrType, "PANGO_ATTR_WEIGHT")
macdef PANGO_ATTR_VARIANT = $extval (PangoAttrType, "PANGO_ATTR_VARIANT")
macdef PANGO_ATTR_STRETCH = $extval (PangoAttrType, "PANGO_ATTR_STRETCH")
macdef PANGO_ATTR_SIZE = $extval (PangoAttrType, "PANGO_ATTR_SIZE")
macdef PANGO_ATTR_FONT_DESC = $extval (PangoAttrType, "PANGO_ATTR_FONT_DESC")
macdef PANGO_ATTR_FOREGROUND = $extval (PangoAttrType, "PANGO_ATTR_FOREGROUND")
macdef PANGO_ATTR_BACKGROUND = $extval (PangoAttrType, "PANGO_ATTR_BACKGROUND")
macdef PANGO_ATTR_UNDERLINE = $extval (PangoAttrType, "PANGO_ATTR_UNDERLINE")
macdef PANGO_ATTR_STRIKETHROUGH = $extval (PangoAttrType, "PANGO_ATTR_STRIKETHROUGH")
macdef PANGO_ATTR_RISE = $extval (PangoAttrType, "PANGO_ATTR_RISE")
macdef PANGO_ATTR_SHAPE = $extval (PangoAttrType, "PANGO_ATTR_SHAPE")
macdef PANGO_ATTR_SCALE = $extval (PangoAttrType, "PANGO_ATTR_SCALE")
macdef PANGO_ATTR_FALLBACK = $extval (PangoAttrType, "PANGO_ATTR_FALLBACK")
macdef PANGO_ATTR_LETTER_SPACING = $extval (PangoAttrType, "PANGO_ATTR_LETTER_SPACING")
macdef PANGO_ATTR_UNDERLINE_COLOR = $extval (PangoAttrType, "PANGO_ATTR_UNDERLINE_COLOR")
macdef PANGO_ATTR_STRIKETHROUGH_COLOR = $extval (PangoAttrType, "PANGO_ATTR_STRIKETHROUGH_COLOR")
macdef PANGO_ATTR_ABSOLUTE_SIZE = $extval (PangoAttrType, "PANGO_ATTR_ABSOLUTE_SIZE")

(* ****** ****** *)

abst@ype PangoUnderline = $extype "PangoUnderline"
macdef PANGO_UNDERLINE_NONE = $extval (PangoUnderline, "PANGO_UNDERLINE_NONE")
macdef PANGO_UNDERLINE_SINGLE = $extval (PangoUnderline, "PANGO_UNDERLINE_SINGLE")
macdef PANGO_UNDERLINE_DOUBLE = $extval (PangoUnderline, "PANGO_UNDERLINE_DOUBLE")
macdef PANGO_UNDERLINE_LOW = $extval (PangoUnderline, "PANGO_UNDERLINE_LOW")
macdef PANGO_UNDERLINE_ERROR = $extval (PangoUnderline, "PANGO_UNDERLINE_ERROR")

(* ****** ****** *)

(* end of [pango-attributes.sats] *)
