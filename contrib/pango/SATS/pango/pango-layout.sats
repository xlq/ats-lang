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

abst@ype PangoAlignment = $extype "PangoAlignment"
macdef PANGO_ALIGN_LEFT = $extval (PangoAlignment, "PANGO_ALIGN_LEFT")
macdef PANGO_ALIGN_CENTER = $extval (PangoAlignment, "PANGO_ALIGN_CENTER")
macdef PANGO_ALIGN_RIGHT = $extval (PangoAlignment, "PANGO_ALIGN_RIGHT")

abst@ype PangoWrapMode = $extype "PangoWrapMode"
macdef PANGO_WRAP_WORD = $extval (PangoWrapMode, "PANGO_WRAP_WORD")
macdef PANGO_WRAP_CHAR = $extval (PangoWrapMode, "PANGO_WRAP_CHAR")
macdef PANGO_WRAP_WORD_CHAR = $extval (PangoWrapMode, "PANGO_WRAP_WORD_CHAR")

abst@ype PangoEllipsizeMode = $extype "PangoEllipsizeMode"
macdef PANGO_ELLIPSIZE_NONE = $extval (PangoEllipsizeMode, "PANGO_ELLIPSIZE_NONE")
macdef PANGO_ELLIPSIZE_START = $extval (PangoEllipsizeMode, "PANGO_ELLIPSIZE_START")
macdef PANGO_ELLIPSIZE_MIDDLE = $extval (PangoEllipsizeMode, "PANGO_ELLIPSIZE_MIDDLE")
macdef PANGO_ELLIPSIZE_END = $extval (PangoEllipsizeMode, "PANGO_ELLIPSIZE_END")

(* ****** ****** *)

fun pango_layout_new (): PangoLayout_ref1 = "#atsctrb_pango_layout_new"

fun pango_layout_copy
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l)): PangoLayout_ref1 = "#atsctrb_pango_layout_copy"
// end of [pango_layout_copy]

(* ****** ****** *)

fun pango_layout_get_size
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), width: &int? >> int, height: &int? >> int): void
  = "#atsctrb_pango_layout_get_size"
// end of [pango_layout_get_size]

fun pango_layout_get_pixel_size
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), width: &int? >> int, height: &int? >> int): void
  = "#atsctrb_pango_layout_get_pixel_size"
// end of [pango_layout_get_pixel_size]

(* ****** ****** *)

fun pango_layout_get_width
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): int = "#atsctrb_pango_layout_get_width"
// end of [pango_layout_get_width]

fun pango_layout_set_width
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), width: int): void
  = "#atsctrb_pango_layout_set_width"
// end of [pango_layout_set_width]

fun pango_layout_get_height
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): int = "#atsctrb_pango_layout_get_height"
// end of [pango_layout_get_height]

fun pango_layout_set_height
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), height: int): void
  = "#atsctrb_pango_layout_set_height"
// end of [pango_layout_set_height]

(* ****** ****** *)

fun pango_layout_get_alignment
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): PangoAlignment
  = "#atsctrb_pango_layout_get_alignment"
// end of [pango_layout_get_alignment]

fun pango_layout_set_alignment
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), knd: PangoAlignment): void
  = "#atsctrb_pango_layout_set_alignment"
// end of [pango_layout_set_alignment]

(* ****** ****** *)

fun pango_layout_get_wrap
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): PangoWrapMode
  = "#atsctrb_pango_layout_get_wrap"
// end of [pango_layout_get_wrap]

fun pango_layout_set_wrap
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), knd: PangoWrapMode): void
  = "#atsctrb_pango_layout_set_wrap"
// end of [pango_layout_set_wrap]

fun pango_layout_is_wrapped
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): gboolean = "#atsctrb_pango_layout_is_wrapped"
// end of [pango_layout_is_wrapped]

(* ****** ****** *)

fun pango_layout_get_ellipsize
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): PangoEllipsizeMode
  = "#atsctrb_pango_layout_get_ellipsize"
// end of [pango_layout_get_ellipsize]

fun pango_layout_set_ellipsize
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), knd: PangoEllipsizeMode): void
  = "#atsctrb_pango_layout_set_ellipsize"
// end of [pango_layout_set_ellipsize]

fun pango_layout_is_ellipsized
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): gboolean = "#atsctrb_pango_layout_is_ellipsized"
// end of [pango_layout_is_ellipsized]

(* ****** ****** *)

fun pango_layout_get_indent
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): int = "#atsctrb_pango_layout_get_indent"
// end of [pango_layout_get_indent]

fun pango_layout_set_indent
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), indent: int): void
  = "#atsctrb_pango_layout_set_indent"
// end of [pango_layout_set_indent]

fun pango_layout_get_spacing
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): int = "#atsctrb_pango_layout_get_spacing"
// end of [pango_layout_get_spacing]

fun pango_layout_set_spacing
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), spacing: int): void
  = "#atsctrb_pango_layout_set_spacing"
// end of [pango_layout_set_spacing]

(* ****** ****** *)

fun pango_layout_get_justify
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): gboolean = "#atsctrb_pango_layout_get_justify"
// end of [pango_layout_get_justify]

fun pango_layout_set_justify
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), justify: gboolean): void
  = "#atsctrb_pango_layout_set_justify"
// end of [pango_layout_set_justify]

fun pango_layout_get_auto_dir
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): gboolean = "#atsctrb_pango_layout_get_auto_dir"
// end of [pango_layout_get_auto_dir]

fun pango_layout_set_auto_dir
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), auto_dir: gboolean): void
  = "#atsctrb_pango_layout_set_auto_dir"
// end of [pango_layout_set_auto_dir]

(* ****** ****** *)

fun pango_layout_get_justify
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): gboolean = "#atsctrb_pango_layout_get_justify"
// end of [pango_layout_get_justify]

fun pango_layout_set_justify
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), justify: gboolean): void
  = "#atsctrb_pango_layout_set_justify"
// end of [pango_layout_set_justify]

(* ****** ****** *)

fun pango_layout_get_single_paragraph_mode
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l): gboolean
  = "#atsctrb_pango_layout_get_single_paragraph_mode"
// end of [pango_layout_get_single_paragraph_mode]

fun pango_layout_set_single_paragraph_mode
  {c:cls | c <= PangoLayout} {l:agz}
  (layout: !gobjref (c, l), setting: gboolean): void
  = "#atsctrb_pango_layout_set_single_paragraph_mode"
// end of [pango_layout_set_single_paragraph_mode]

(* ****** ****** *)

(* end of [pango-layout.sats] *)

