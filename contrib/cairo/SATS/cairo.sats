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
// Starting time: December, 2009

(* ****** ****** *)

%{#
#include "contrib/cairo/CATS/cairo.cats"
%}

(* ****** ****** *)

// a reference to cairo drawing context
absviewtype cairo_ref // cairo_t*

absviewtype cairo_surface_ref // cairo_surface*
absviewtype cairo_pattern_ref // cairo_pattern*

absviewtype cairo_font_face_ref // cairo_font_face*

(* ****** ****** *)

abst@ype cairo_matrix_t = $extype "ats_cairo_matrix_type"

(* ****** ****** *)

// enum type
abst@ype cairo_status_t = $extype "ats_cairo_status_type"
castfn int_of_cairo_status_t (x: cairo_status_t):<> int

macdef CAIRO_STATUS_SUCCESS =
  $extval (cairo_status_t, "CAIRO_STATUS_SUCCESS")

macdef CAIRO_STATUS_NO_MEMORY =
  $extval (cairo_status_t, "CAIRO_STATUS_NO_MEMORY")

macdef CAIRO_STATUS_INVALID_RESTORE =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_RESTORE")

macdef CAIRO_STATUS_INVALID_POP_GROUP =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_POP_GROUP")

macdef CAIRO_STATUS_NO_CURRENT_POINT =
  $extval (cairo_status_t, "CAIRO_STATUS_NO_CURRENT_POINT")

macdef CAIRO_STATUS_INVALID_MATRIX =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_MATRIX")

macdef CAIRO_STATUS_INVALID_STATUS =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_STATUS")

macdef CAIRO_STATUS_NULL_POINTER =
  $extval (cairo_status_t, "CAIRO_STATUS_NULL_POINTER")

macdef CAIRO_STATUS_INVALID_STRING =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_STRING")

macdef CAIRO_STATUS_INVALID_PATH_DATA =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_PATH_DATA")

macdef CAIRO_STATUS_READ_ERROR =
  $extval (cairo_status_t, "CAIRO_STATUS_READ_ERROR")

macdef CAIRO_STATUS_WRITE_ERROR =
  $extval (cairo_status_t, "CAIRO_STATUS_WRITE_ERROR")

macdef CAIRO_STATUS_SURFACE_FINISHED =
  $extval (cairo_status_t, "CAIRO_STATUS_SURFACE_FINISHED")

macdef CAIRO_STATUS_SURFACE_TYPE_MISMATCH =
  $extval (cairo_status_t, "CAIRO_STATUS_SURFACE_TYPE_MISMATCH")

macdef CAIRO_STATUS_PATTERN_TYPE_MISMATCH =
  $extval (cairo_status_t, "CAIRO_STATUS_PATTERN_TYPE_MISMATCH")

macdef CAIRO_STATUS_INVALID_CONTENT =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_CONTENT")

macdef CAIRO_STATUS_INVALID_FORMAT =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_FORMAT")

macdef CAIRO_STATUS_INVALID_VISUAL =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_VISUAL")

macdef CAIRO_STATUS_FILE_NOT_FOUND =
  $extval (cairo_status_t, "CAIRO_STATUS_FILE_NOT_FOUND")

macdef CAIRO_STATUS_INVALID_DASH =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_DASH")

macdef CAIRO_STATUS_INVALID_DSC_COMMENT =
  $extval (cairo_status_t, "CAIRO_STATUS_INVALID_DSC_COMMENT")

fun eq_cairo_status_cairo_status
  (x1: cairo_status_t, x2: cairo_status_t): bool
  = "atsctrb_eq_cairo_status_cairo_status"
overload = with eq_cairo_status_cairo_status

(* ****** ****** *)

// enum type
abst@ype cairo_operator_t = $extype "ats_cairo_operator_type"
castfn int_of_cairo_operator_t (x: cairo_operator_t):<> int

(* ****** ****** *)

// enum type
abst@ype cairo_format_t = $extype "ats_cairo_format_type"
castfn int_of_cairo_format_t (x: cairo_format_t):<> int

macdef CAIRO_FORMAT_ARGB32 =
  $extval (cairo_format_t, "CAIRO_FORMAT_ARGB32")

macdef CAIRO_FORMAT_RGB24 =
  $extval (cairo_format_t, "CAIRO_FORMAT_RGB24")

macdef CAIRO_FORMAT_A8 =
  $extval (cairo_format_t, "CAIRO_FORMAT_A8")

macdef CAIRO_FORMAT_A1 =
  $extval (cairo_format_t, "CAIRO_FORMAT_A1")

(*
macdef CAIRO_FORMAT_RGB16_565 = // deprecated!
  $extval (cairo_format_t, "CAIRO_FORMAT_RGB16_565")
*)

(* ****** ****** *)

// enum type
abst@ype cairo_font_slant_t = $extype "ats_cairo_font_slant_type"
castfn int_of_cairo_font_slant_t (x: cairo_font_slant_t):<> int

macdef CAIRO_FONT_SLANT_NORMAL =
  $extval (cairo_font_slant_t, "CAIRO_FONT_SLANT_NORMAL")

macdef CAIRO_FONT_SLANT_ITALIC =
  $extval (cairo_font_slant_t, "CAIRO_FONT_SLANT_ITALIC")

macdef CAIRO_FONT_SLANT_OBLIQUE =
  $extval (cairo_font_slant_t, "CAIRO_FONT_SLANT_OBLIQUE")

// enum type
abst@ype cairo_font_weight_t = $extype "ats_cairo_font_weight_type"
castfn int_of_cairo_font_weight_t (x: cairo_font_weight_t):<> int

macdef CAIRO_FONT_WEIGHT_NORMAL =
  $extval (cairo_font_weight_t, "CAIRO_FONT_WEIGHT_NORMAL")

macdef CAIRO_FONT_WEIGHT_BOLD =
  $extval (cairo_font_weight_t, "CAIRO_FONT_WEIGHT_BOLD")

(* ****** ****** *)

absview cairo_save_v // abstract view generated by cairo_save
absview cairo_push_group_v // abstract view generated by cairo_push_group

(* ****** ****** *)

//
// contexts for drawing
//

(* ****** ****** *)

fun cairo_create
  (sf: !cairo_surface_ref): cairo_ref
  = "atsctrb_cairo_create"

fun cairo_reference (cr: !cairo_ref): cairo_ref
  = "atsctrb_cairo_reference"

fun cairo_destroy (cr: cairo_ref): void
  = "atsctrb_cairo_destroy"

//

fun cairo_status (cr: !cairo_ref): cairo_status_t
  = "atsctrb_cairo_status"

(* ****** ****** *)

fun cairo_save (cr: !cairo_ref): (cairo_save_v | void)
  = "atsctrb_cairo_save"

fun cairo_restore (pf: cairo_save_v | cr: !cairo_ref): void
  = "atsctrb_cairo_restore"

(* ****** ****** *)

fun cairo_get_target (cr: !cairo_ref): cairo_surface_ref
  = "atsctrb_cairo_get_target"

fun cairo_get_group_target
  (cr: !cairo_ref): cairo_surface_ref
  = "atsctrb_cairo_get_group_target"

(* ****** ****** *)

fun cairo_push_group
  (cr: !cairo_ref): (cairo_push_group_v | void)
  = "atsctrb_cairo_push_group"

(*
void cairo_push_group_with_content
(cairo_t *cr, cairo_content_t content);
*)

fun cairo_pop_group
  (pf: cairo_push_group_v | cr: !cairo_ref): cairo_pattern_ref
  = "atsctrb_cairo_pop_group"

fun cairo_pop_group_to_source
  (pf: cairo_push_group_v | cr: !cairo_ref): void
  = "atsctrb_cairo_pop_group_to_source"

(* ****** ****** *)

fun cairo_set_source_rgb (
    cr: !cairo_ref
  , red: double, green: double, blue: double
  ) : void
  = "atsctrb_cairo_set_source_rgb"
// end of [cairo_set_source_rgb]

fun cairo_set_source_rgba (
    cr: !cairo_ref
  , red: double, green: double, blue: double, alpha: double
  ) : void
  = "atsctrb_cairo_set_source_rgba"
// end of [cairo_set_source_rgba]

fun cairo_get_source
  (cr: !cairo_ref): cairo_pattern_ref
  = "atsctrb_cairo_get_source"

fun cairo_set_source
  (cr: !cairo_ref, source: !cairo_pattern_ref): void
  = "atsctrb_cairo_set_source"

fun cairo_set_source_surface
  (cr: !cairo_ref, sf: !cairo_surface_ref, x: double, y: double): void
  = "atsctrb_cairo_set_source_surface"

(* ****** ****** *)

fun cairo_get_line_width (cr: !cairo_ref): double
  = "atsctrb_cairo_get_line_width"

fun cairo_set_line_width (cr: !cairo_ref, width: double): void
  = "atsctrb_cairo_set_line_width"
                                                         
(* ****** ****** *)

fun cairo_fill (cr: !cairo_ref): void
  = "atsctrb_cairo_fill"

fun cairo_fill_preserve (cr: !cairo_ref): void
  = "atsctrb_cairo_fill_preserve"

fun cairo_fill_extents (
    cr: !cairo_ref
  , x1: double, y1: double, x2: double, y2: double
  ) : void
  = "atsctrb_cairo_fill_extents"

(* ****** ****** *)

fun cairo_paint (cr: !cairo_ref): void
  = "atsctrb_cairo_paint"

fun cairo_paint_with_alpha (cr: !cairo_ref, alpha: double): void
  = "atsctrb_cairo_paint_with_alpha"

(* ****** ****** *)

fun cairo_mask (cr: !cairo_ref, pattern: !cairo_pattern_ref): void
  = "atsctrb_cairo_mask"

fun cairo_mask_surface (
    cr: !cairo_ref
  , sf: !cairo_surface_ref, surface_x: double, surface_y: double
  ) : void
  = "atsctrb_cairo_mask_surface"

(* ****** ****** *)

fun cairo_stroke (cr: !cairo_ref): void
  = "atsctrb_cairo_stroke"

fun cairo_stroke_preserve (cr: !cairo_ref): void
  = "atsctrb_cairo_stroke_preserve"

fun cairo_stroke_extents (
    cr: !cairo_ref
  , x1: double, y1: double, x2: double, y2: double
  ) : void
  = "atsctrb_cairo_stroke_extents"

(* ****** ****** *)

fun cairo_get_reference_count (cr: !cairo_ref): uint
  = "atsctrb_cairo_get_reference_count"

(* ****** ****** *)

//
// drawing paths
//

fun cairo_curve_to (
    cr: !cairo_ref
  , x1: double, y1: double
  , x2: double, y2: double
  , x3: double, x4: double
  ) : void
  = "atsctrb_cairo_curve_to"

fun cairo_line_to
  (cr: !cairo_ref, x: double, y: double): void
  = "atsctrb_cairo_line_to"

fun cairo_move_to
  (cr: !cairo_ref, x: double, y: double): void
  = "atsctrb_cairo_move_to"

fun cairo_rectangle (
    cr: !cairo_ref
  , x: double, y: double, width: double, height: double
  ) : void
  = "atsctrb_cairo_rectangle"

(* ****** ****** *)

// drawing texts

fun cairo_select_font_face (
    cr: !cairo_ref
  , name: string (* family *)
  , slnt: cairo_font_slant_t
  , wght: cairo_font_weight_t
  ) : void
  = "atsctrb_cairo_select_font_face"

fun cairo_set_font_size
  (cr: !cairo_ref, size: double): void
  = "atsctrb_cairo_set_font_size"

(* ****** ****** *)

fun cairo_get_font_face
  (cr: !cairo_ref): cairo_font_face_ref
  = "atsctrb_cairo_get_font_face"

fun cairo_set_font_face
  (cr: !cairo_ref, face: !cairo_font_face_ref): void
  = "atsctrb_cairo_set_font_face"

(* ****** ****** *)

fun cairo_show_text (cr: !cairo_ref, utf8: string): void
  = "atsctrb_cairo_show_text"

(* ****** ****** *)

// transformations for drawing

fun cairo_translate
  (cr: !cairo_ref, x: double, y: double): void
  = "atsctrb_cairo_translate"

fun cairo_scale (cr: !cairo_ref, sx: double, sy: double): void
  = "atsctrb_cairo_scale"

fun cairo_rotate (cr: !cairo_ref, angle: double): void
  = "atsctrb_cairo_rotate"
  
(* ****** ****** *)

//
// surfaces for drawing
//

(* ****** ****** *)

fun cairo_surface_destroy
  (sf: cairo_surface_ref): void
  = "atsctrb_cairo_surface_destroy"

(* ****** ****** *)

//
// image surface
//

(*
// how to handle this:
#define CAIRO_HAS_IMAGE_SURFACE
*)

fun cairo_format_stride_for_width
  (format: cairo_format_t, width: int): int
  = "atsctrb_cairo_format_stride_for_width"

fun cairo_image_surface_create (
    format: cairo_format_t, width: int, height: int
  ) : cairo_surface_ref
  = "atsctrb_cairo_image_surface_create"

(*
cairo_surface_t*
cairo_image_surface_create_for_data (
  unsigned char *data,
  cairo_format_t format,
  int width, int height, int stride
) ;

unsigned char*
cairo_image_surface_get_data (cairo_surface_t *surface);
*)

fun cairo_image_surface_get_format
  (sf: !cairo_surface_ref): cairo_format_t
  = "atsctrb_cairo_image_surface_get_format"

fun cairo_image_surface_get_width (sf: !cairo_surface_ref): int
  = "atsctrb_cairo_image_surface_get_width"

fun cairo_image_surface_get_height (sf: !cairo_surface_ref): int
  = "atsctrb_cairo_image_surface_get_height"

fun cairo_image_surface_get_stride (sf: !cairo_surface_ref): int
  = "atsctrb_cairo_image_surface_get_stride"

fun cairo_surface_write_to_png
  (sf: !cairo_surface_ref, filename: string): cairo_status_t
  = "atsctrb_cairo_surface_write_to_png"

(* ****** ****** *)

//
// utilities for drawing
//

(* ****** ****** *)

// generic matrix operations

fun cairo_matrix_init (
    matrix: &cairo_matrix_t? >> cairo_matrix_t
  , xx: double, yx: double, xy: double, yy: double
  , x0: double, y0: double
  ) : void
  = "cairo_matrix_init"

(* ****** ****** *)

fun cairo_matrix_init_identity
  (matrix: &cairo_matrix_t? >> cairo_matrix_t): void
  = "cairo_matrix_init_identity"

fun cairo_matrix_init_translate (
    matrix: &cairo_matrix_t? >> cairo_matrix_t, tx: double, ty: double
  ) : void
  = "cairo_matrix_init_translate"

fun cairo_matrix_init_scale (
    matrix: &cairo_matrix_t? >> cairo_matrix_t, sx: double, sy: double
  ) : void
  = "cairo_matrix_init_scale"

fun cairo_matrix_init_rotate (
    matrix: &cairo_matrix_t? >> cairo_matrix_t, angle: double
  ) : void
  = "cairo_matrix_init_rotate"

(* ****** ****** *)

fun cairo_matrix_translate (
    matrix: &cairo_matrix_t >> cairo_matrix_t, tx: double, ty: double
  ) : void
  = "cairo_matrix_translate"

fun cairo_matrix_scale (
    matrix: &cairo_matrix_t >> cairo_matrix_t, sx: double, sy: double
  ) : void
  = "cairo_matrix_scale"

fun cairo_matrix_rotate (
    matrix: &cairo_matrix_t >> cairo_matrix_t, angle: double
  ) : void
  = "cairo_matrix_rotate"

(* ****** ****** *)

fun cairo_matrix_invert (
    matrix: &cairo_matrix_t >> cairo_matrix_t
  ) : cairo_status_t
  = "cairo_matrix_invert"

fun cairo_matrix_multiply (
    result: &cairo_matrix_t? >> cairo_matrix_t
  , amatrix: &cairo_matrix_t (*read*)
  , bmatrix: &cairo_matrix_t (*read*)
  ) : void
  = "cairo_matrix_multiply"

fun cairo_matrix_transform_distance (
    matrix: &cairo_matrix_t (*read*), dx: &double, dy: &double
  ) : void
  = "cairo_matrix_transform_distance"

fun cairo_matrix_transform_point (
    matrix: &cairo_matrix_t (*read*), x: &double, y: &double
  ) : void
  = "cairo_matrix_transform_point"

(* ****** ****** *)

(* end of [cairo.sats] *)
