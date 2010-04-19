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

//
// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: December, 2009
//

(* ****** ****** *)
  
//
// API for cairo in ATS
//

(* ****** ****** *)

%{#
#include "contrib/cairo/CATS/cairo.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

// a reference to cairo drawing context
// [cairo_ref] is reference counted
absviewtype cairo_ref (l:addr) // cairo_t* != null
viewtypedef cairo_ref1 = [l:addr | l > null] cairo_ref l

// [cairo_surface_ref] is reference counted
absviewtype cairo_surface_ref (l:addr) // cairo_surface* != null
viewtypedef cairo_surface_ref1 = [l:addr | l > null] cairo_surface_ref l

// [cairo_pattern_ref] is reference counted
absviewtype cairo_pattern_ref (l:addr) // cairo_pattern* != null
viewtypedef cairo_pattern_ref1 = [l:addr | l > null] cairo_pattern_ref l

// [cairo_font_face_ref] is reference counted
absviewtype cairo_font_face_ref (l:addr) // cairo_font_face* != null
viewtypedef cairo_font_face_ref1 = [l:addr | l > null] cairo_font_face_ref l

// [cairo_font_options_ptr] is not reference counted
absviewtype cairo_font_options_ptr (l:addr) // cairo_font_options_ptr != null
viewtypedef cairo_font_options_ptr1 = [l:addr | l > null] cairo_font_options_ptr l

(* ****** ****** *)

abst@ype cairo_matrix_t = $extype "cairo_matrix_t"

(* ****** ****** *)

// enum type
abst@ype cairo_status_t = $extype "cairo_status_t"
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
abst@ype cairo_format_t = $extype "cairo_format_t"
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

absview cairo_save_v (l:addr) // abstract view generated by cairo_save
absview cairo_push_group_v (l:addr) // abstract view generated by cairo_push_group

(* ****** ****** *)

//
// contexts for drawing
//

(* ****** ****** *)

fun cairo_create {l:agz}
  (sf: !cairo_surface_ref l): cairo_ref1 = "#atsctrb_cairo_create"
// end of [cairo_create]

fun cairo_reference
  {l:agz} (cr: !cairo_ref l): cairo_ref l = "#atsctrb_cairo_reference"
// end of [cairo_reference]

fun cairo_destroy (cr: cairo_ref1): void = "#atsctrb_cairo_destroy"

fun cairo_status
  {l:agz} (cr: !cairo_ref l): cairo_status_t = "#atsctrb_cairo_status"
// end of [cairo_status]

(* ****** ****** *)

fun cairo_save {l:agz}
  (cr: !cairo_ref l): (cairo_save_v l | void) = "#atsctrb_cairo_save"
// end of [cairo_save]

fun cairo_restore {l:agz}
  (pf: cairo_save_v l | cr: !cairo_ref l): void = "#atsctrb_cairo_restore"
// end of [cairo_restore]

(* ****** ****** *)

fun cairo_get_target
  {l1:agz} (cr: !cairo_ref l1): [l2:agz] (
    minus (cairo_ref l1, cairo_surface_ref l2) | cairo_surface_ref l2
  ) = "#atsctrb_cairo_get_target"
// end of [cairo_get_target]

fun cairo_get_group_target
  {l1:agz} (cr: !cairo_ref l1): [l2:agz] (
    minus (cairo_ref l1, cairo_surface_ref l2) | cairo_surface_ref l2
  ) = "#atsctrb_cairo_get_group_target"
// end of [cairo_get_group_target]

//
// HX-2010-01-23:
// note that these two functions are slightly different from
// the original ones in cairo in terms of reference counting
//
fun cairo_get_target1
  {l:agz} (cr: !cairo_ref l)
  : cairo_surface_ref1 = "atsctrb_cairo_get_target1" // function!
// end of [cairo_get_target1]

fun cairo_get_group_target1
  {l:agz} (cr: !cairo_ref l)
  : cairo_surface_ref1 = "atsctrb_cairo_get_group_target1" // function!
// end of [cairo_get_group_target1

(* ****** ****** *)

fun cairo_push_group {l:agz}
  (cr: !cairo_ref l): (cairo_push_group_v l | void)
  = "#atsctrb_cairo_push_group"

// enum type
abst@ype cairo_content_t = $extype "cairo_content_t"

macdef CAIRO_CONTENT_COLOR =
  $extval (cairo_content_t, "CAIRO_CONTENT_COLOR")

macdef CAIRO_CONTENT_ALPHA =
  $extval (cairo_content_t, "CAIRO_CONTENT_ALPHA")

macdef CAIRO_CONTENT_COLOR_ALPHA =
  $extval (cairo_content_t, "CAIRO_CONTENT_COLOR_ALPHA")

fun cairo_push_group_with_content
  {l:agz} (
    cr: !cairo_ref l, content: cairo_content_t
  ) : (cairo_push_group_v l | void)
  = "#atsctrb_cairo_push_group_with_content"

fun cairo_pop_group {l:agz}
  (pf: cairo_push_group_v l | cr: !cairo_ref l): cairo_pattern_ref1
  = "#atsctrb_cairo_pop_group"

fun cairo_pop_group_to_source {l:agz}
  (pf: cairo_push_group_v l | cr: !cairo_ref l): void
  = "#atsctrb_cairo_pop_group_to_source"

(* ****** ****** *)

fun cairo_set_source_rgb {l:agz} (
    cr: !cairo_ref l
  , red: double, green: double, blue: double
  ) : void
  = "#atsctrb_cairo_set_source_rgb"
// end of [cairo_set_source_rgb]

fun cairo_set_source_rgba {l:agz} (
    cr: !cairo_ref l
  , red: double, green: double, blue: double, alpha: double
  ) : void
  = "#atsctrb_cairo_set_source_rgba"
// end of [cairo_set_source_rgba]

(* ****** ****** *)

fun cairo_get_source {l:agz}
  (cr: !cairo_ref l): cairo_pattern_ref1 = "#atsctrb_cairo_get_source"
// end of [cairo_get_source]

fun cairo_set_source {l1,l2:agz}
  (cr: !cairo_ref l1, pat: !cairo_pattern_ref l2): void
  = "#atsctrb_cairo_set_source"

fun cairo_set_source_surface {l1,l2:agz} (
    cr: !cairo_ref l1, sf: !cairo_surface_ref l2, x: double, y: double
  ) : void = "#atsctrb_cairo_set_source_surface"
// end of [cairo_set_source_surface]

(* ****** ****** *)

abst@ype cairo_antialias_t = $extype "cairo_antialias_t"

macdef CAIRO_ANTIALIAS_DEFAULT =
  $extval (cairo_antialias_t, "CAIRO_ANTIALIAS_DEFAULT")
macdef CAIRO_ANTIALIAS_NONE =
  $extval (cairo_antialias_t, "CAIRO_ANTIALIAS_NONE")
macdef CAIRO_ANTIALIAS_GRAY =
  $extval (cairo_antialias_t, "CAIRO_ANTIALIAS_GRAY")
macdef CAIRO_ANTIALIAS_SUBPIXEL =
  $extval (cairo_antialias_t, "CAIRO_ANTIALIAS_SUBPIXEL")

fun cairo_get_antialias
  {l:agz} (cr: !cairo_ref l): cairo_antialias_t
  = "#atsctrb_cairo_get_antialias"

fun cairo_set_antialias
  {l:agz} (cr: !cairo_ref l, antialias: cairo_antialias_t): void
  = "#atsctrb_cairo_set_antialias"

(* ****** ****** *)

fun cairo_get_dash_count
  {l:agz} (cr: !cairo_ref l): int = "#atsctrb_cairo_get_dash_count"
// end of [cairo_get_dash_count]

//
// note that [dashes] gets updated only if [n1 <= n]
//
fun cairo_get_dash {l:agz} {n:nat} (
    cr: !cairo_ref l
  , dashes: &(@[double][n]), n: int n, offset: &double? >> double
  ) : [n1:nat] int n1
  = "atsctrb_cairo_get_dash" // this is a function!

fun cairo_set_dash {l:agz} {n:nat} (
    cr: !cairo_ref l, dashes: &(@[double][n]), n: int n, offset: double
  ) : void
  = "#atsctrb_cairo_set_dash"

(* ****** ****** *)

// enum type
abst@ype cairo_fill_rule_t = $extype "cairo_fill_rule_t"

macdef CAIRO_FILL_RULE_WINDING =
  $extval (cairo_fill_rule_t, "CAIRO_FILL_RULE_WINDING")
macdef CAIRO_FILL_RULE_EVEN_ODD =
  $extval (cairo_fill_rule_t, "CAIRO_FILL_RULE_EVEN_ODD")

fun cairo_get_fill_rule {l:agz}
  (cr: !cairo_ref l): cairo_fill_rule_t = "#atsctrb_cairo_get_fill_rule"
// end of [cairo_get_fill_rule]

fun cairo_set_fill_rule
  {l:agz} (cr: !cairo_ref l, fill_rule: cairo_fill_rule_t)
  : void = "#atsctrb_cairo_set_fill_rule"
// end of [cairo_set_fill_rule]

(* ****** ****** *)

// enum type
abst@ype cairo_line_cap_t = $extype "cairo_line_cap_t"

macdef CAIRO_LINE_CAP_BUTT =
  $extval (cairo_line_cap_t, "CAIRO_LINE_CAP_BUTT")

macdef CAIRO_LINE_CAP_ROUND =
  $extval (cairo_line_cap_t, "CAIRO_LINE_CAP_ROUND")

macdef CAIRO_LINE_CAP_SQUARE =
  $extval (cairo_line_cap_t, "CAIRO_LINE_CAP_SQUARE")

fun cairo_get_line_cap
  {l:agz} (cr: !cairo_ref l): cairo_line_cap_t
  = "#atsctrb_cairo_get_line_cap"
// end of [cairo_get_line_cap]

fun cairo_set_line_cap
  {l:agz} (cr: !cairo_ref l, line_cap: cairo_line_cap_t): void
  = "#atsctrb_cairo_set_line_cap"
// end of [cairo_set_line_cap]

(* ****** ****** *)

// enum type
abst@ype cairo_line_join_t = $extype "cairo_line_join_t"

macdef CAIRO_LINE_JOIN_MITER =
  $extval (cairo_line_join_t, "CAIRO_LINE_JOIN_MITER")

macdef CAIRO_LINE_JOIN_ROUND =
  $extval (cairo_line_join_t, "CAIRO_LINE_JOIN_ROUND")

macdef CAIRO_LINE_JOIN_BEVEL =
  $extval (cairo_line_join_t, "CAIRO_LINE_JOIN_BEVEL")

fun cairo_get_line_join
  {l:agz} (cr: !cairo_ref l): cairo_line_join_t
  = "#atsctrb_cairo_get_line_join"

fun cairo_set_line_join
  {l:agz} (cr: !cairo_ref l, line_join: cairo_line_join_t): void
  = "#atsctrb_cairo_set_line_join"

(* ****** ****** *)

fun cairo_get_line_width
  {l:agz} (cr: !cairo_ref l): double = "#atsctrb_cairo_get_line_width"
// end of [cairo_get_line_width]

fun cairo_set_line_width
  {l:agz} (cr: !cairo_ref l, width: double): void = "#atsctrb_cairo_set_line_width"
// end of [cairo_set_line_width]

(* ****** ****** *)

fun cairo_get_miter_limit
  {l:agz} (cr: !cairo_ref l): double = "#atsctrb_cairo_get_miter_limit"
// end of [cairo_get_miter_limit]

fun cairo_set_miter_limit
  {l:agz} (cr: !cairo_ref l, width: double): void = "#atsctrb_cairo_set_miter_limit"
// end of [cairo_set_miter_limit]

(* ****** ****** *)

// enum type
abst@ype cairo_operator_t = $extype "cairo_operator_t"
castfn int_of_cairo_operator_t (x: cairo_operator_t):<> int

macdef CAIRO_OPERATOR_CLEAR =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_CLEAR")

macdef CAIRO_OPERATOR_SOURCE =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_SOURCE")

macdef CAIRO_OPERATOR_OVER =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_OVER")

macdef CAIRO_OPERATOR_IN =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_IN")

macdef CAIRO_OPERATOR_OUT =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_OUT")

macdef CAIRO_OPERATOR_ATOP =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_ATOP")

macdef CAIRO_OPERATOR_DEST =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_DEST")

macdef CAIRO_OPERATOR_DEST_OVER =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_DEST_OVER")

macdef CAIRO_OPERATOR_DEST_IN =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_DEST_IN")

macdef CAIRO_OPERATOR_DEST_OUT =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_DEST_OUT")

macdef CAIRO_OPERATOR_DEST_ATOP =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_DEST_ATOP")

macdef CAIRO_OPERATOR_XOR =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_XOR")

macdef CAIRO_OPERATOR_ADD =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_ADD")

macdef CAIRO_OPERATOR_SATURATE =
  $extval (cairo_operator_t, "CAIRO_OPERATOR_SATURATE")

fun cairo_get_operator
  {l:agz} (cr: !cairo_ref l): cairo_operator_t
  = "#atsctrb_cairo_get_operator"

fun cairo_set_operator
  {l:agz} (cr: !cairo_ref l, operator: cairo_operator_t): void
  = "#atsctrb_cairo_set_operator"

(* ****** ****** *)

fun cairo_get_tolerance {l:agz} (cr: !cairo_ref l): double
  = "#atsctrb_cairo_get_tolerance"

fun cairo_set_tolerance {l:agz} (cr: !cairo_ref l, tolerance: double): void
  = "#atsctrb_cairo_set_tolerance"

(* ****** ****** *)

(*
// this would be of great inconvenience!
abst@ype cairo_rectangle_t = $extype "cairo_rectangle_t"
*)
typedef cairo_rectangle_t =
  $extype_struct "cairo_rectangle_t" of {
  x= double, y= double, width= double, height= double
} // end of [cairo_rectangel_t]

(* ****** ****** *)

absviewtype // [n]: list length
cairo_rectangle_list_ref (n:int) // cairo_rectangle_list_t*

fun cairo_rectangle_list_destroy
  {n:nat} (lst: cairo_rectangle_list_ref (n)): void
  = "#atsctrb_cairo_rectangle_list_destroy"

fun cairo_copy_clip_rectangle_list
  {l:agz} (cr: !cairo_ref l): [n:nat] cairo_rectangle_list_ref (n)
  = "#atsctrb_cairo_copy_clip_rectangle_list"

(* ****** ****** *)

fun cairo_clip
  {l:agz} (cr: !cairo_ref l): void = "#atsctrb_cairo_clip"
// end of [cairo_clip]

fun cairo_clip_preserve
  {l:agz} (cr: !cairo_ref l): void = "#atsctrb_cairo_clip_preserve"
// end of [cairo_clip_preserve]

fun cairo_clip_extents
  {l:agz} (
    cr: !cairo_ref l
  , x1: &double? >> double
  , y1: &double? >> double
  , x2: &double? >> double
  , y2: &double? >> double
  ) : void
  = "#atsctrb_cairo_clip_extents"
// end of [cairo_clip_extents]

fun cairo_reset_clip
  {l:agz} (cr: !cairo_ref l): void = "#atsctrb_cairo_reset_clip"
// end of [cairo_reset_clip]

(* ****** ****** *)

fun cairo_fill
  {l:agz} (cr: !cairo_ref l): void = "#atsctrb_cairo_fill"
// end of [cairo_fill]

fun cairo_fill_preserve
  {l:agz} (cr: !cairo_ref l): void = "#atsctrb_cairo_fill_preserve"
// end of [cairo_fill_preserve]

fun cairo_fill_extents
  {l:agz} (
    cr: !cairo_ref l
  , x1: &double? >> double
  , y1: &double? >> double
  , x2: &double? >> double
  , y2: &double? >> double
  ) : void
  = "#atsctrb_cairo_fill_extents"
// end of [cairo_fill_extents]

// [cairo_bool_t] and [bool] are the same
fun cairo_in_fill {l:agz} 
  (cr: !cairo_ref l, x: double, y: double): bool
  = "#atsctrb_cairo_in_fill"
// end of [cairo_in_fill]

(* ****** ****** *)

fun cairo_mask {l1,l2:agz}
  (cr: !cairo_ref l1, pattern: !cairo_pattern_ref l2): void
  = "#atsctrb_cairo_mask"
// end of [cairo_mask]

fun cairo_mask_surface
  {l1,l2:agz} (
    cr: !cairo_ref l1
  , sf: !cairo_surface_ref l2, surface_x: double, surface_y: double
  ) : void
  = "#atsctrb_cairo_mask_surface"
// end of [cairo_mask_surface]

(* ****** ****** *)

fun cairo_paint
  {l:agz} (cr: !cairo_ref l): void = "#atsctrb_cairo_paint"
// end of [cairo_paint]

fun cairo_paint_with_alpha
  {l:agz} (cr: !cairo_ref l, alpha: double): void
  = "#atsctrb_cairo_paint_with_alpha"
// end of [cairo_paint_with_alpha]

(* ****** ****** *)

fun cairo_stroke
  {l:agz} (cr: !cairo_ref l): void = "#atsctrb_cairo_stroke"
// end of [cairo_stroke]

fun cairo_stroke_preserve
  {l:agz} (cr: !cairo_ref l): void = "#atsctrb_cairo_stroke_preserve"
// end of [cairo_stroke_preserve]

fun cairo_stroke_extents
  {l:agz} (
    cr: !cairo_ref l
  , x1: &double? >> double
  , y1: &double? >> double
  , x2: &double? >> double
  , y2: &double? >> double
  ) : void
  = "#atsctrb_cairo_stroke_extents"
// end of [cairo_stroke_extents]

// [cairo_bool_t] and [bool] are the same
fun cairo_in_stroke
  {l:agz} (cr: !cairo_ref l, x: double, y: double): bool
  = "#atsctrb_cairo_in_stroke"
// end of [cairo_in_stroke]

(* ****** ****** *)

fun cairo_get_reference_count
  {l:agz} (cr: !cairo_ref l): uint = "#atsctrb_cairo_get_reference_count"
// end of [cairo_get_reference_count]

(* ****** ****** *)

fun cairo_copy_page
  {l:agz} (cr: !cairo_ref l): void = "#atsctrb_cairo_copy_page"
// end of [cairo_copy_page]

fun cairo_show_page
  {l:agz} (cr: !cairo_ref l): void = "#atsctrb_cairo_show_page"
// end of [cairo_show_page]

(* ****** ****** *)

abst@ype cairo_user_data_key_t = $extype "cairo_user_data_key_t"

//
// note: this interface is unsafe!!!
//
fun cairo_set_user_data
  {l:agz} (
    cr: !cairo_ref l
  , key: &cairo_user_data_key_t
  , user_data: ptr (* the proof of its view is aborbed into [cr] *)
  , destroy_func: ptr -<fun1> void
  ) : cairo_status_t
  = "#atsctrb_cairo_set_user_data"

fun cairo_get_user_data {l:agz} (
    cr: !cairo_ref l, key: &cairo_user_data_key_t
  ) : Ptr
  = "#atsctrb_cairo_get_user_data"

(* ****** ****** *)

//
// drawing paths
//

(* ****** ****** *)

absviewtype // [n]: path length
cairo_path_ref (n:int) // cairo_path_t*

fun cairo_copy_path
  {l:agz} (cr: !cairo_ref l): [n:nat] cairo_path_ref n
  = "#atsctrb_cairo_copy_path"

fun cairo_copy_path_flat
  {l:agz} (cr: !cairo_ref l): [n:nat] cairo_path_ref n
  = "#atsctrb_cairo_copy_path_flat"

fun cairo_append_path {l:agz} {n:nat}
  (cr: !cairo_ref l, path: !cairo_path_ref n): void
  = "#atsctrb_cairo_append_path"

fun cairo_path_destroy {n:nat} (path: cairo_path_ref n): void
  = "#atsctrb_cairo_path_destroy"

(* ****** ****** *)

// [cairo_bool_t] and [bool] are the same
fun cairo_has_current_point {l:agz} (cr: !cairo_ref l): bool
  = "#atsctrb_cairo_has_current_point"

fun cairo_get_current_point {l:agz} (
    cr: !cairo_ref l, x: &double? >> double, y: &double? >> double
  ) : void
  = "#atsctrb_cairo_get_current_point"

(* ****** ****** *)

fun cairo_new_path {l:agz} (cr: !cairo_ref l): void
  = "#atsctrb_cairo_new_path"

fun cairo_new_sub_path {l:agz} (cr: !cairo_ref l): void
  = "#atsctrb_cairo_new_path"

fun cairo_close_path {l:agz} (cr: !cairo_ref l): void
  = "#atsctrb_cairo_close_path"

(* ****** ****** *)

fun cairo_arc
  {l:agz} (
    cr: !cairo_ref l
  , xc: double, yc: double
  , rad: double, angle1: double, angle2: double
  ) : void
  = "#atsctrb_cairo_arc"
// end of [cairo_arc]

fun cairo_arc_negative
  {l:agz} (
    cr: !cairo_ref l
  , xc: double, yc: double
  , rad: double, angle1: double, angle2: double
  ) : void
  = "#atsctrb_cairo_arc_negative"
// end of [cairo_arc_negative]

fun cairo_curve_to
  {l:agz} (
    cr: !cairo_ref l
  , x1: double, y1: double
  , x2: double, y2: double
  , x3: double, y3: double
  ) : void
  = "#atsctrb_cairo_curve_to"
// end of [cairo_curve_to]

fun cairo_line_to
  {l:agz} (cr: !cairo_ref l, x: double, y: double): void
  = "#atsctrb_cairo_line_to"
// end of [cairo_line_to]

fun cairo_move_to
  {l:agz} (cr: !cairo_ref l, x: double, y: double): void
  = "#atsctrb_cairo_move_to"
// end of [cairo_move_to]

fun cairo_rectangle
  {l:agz} (
    cr: !cairo_ref l
  , x: double, y: double, width: double, height: double
  ) : void = "#atsctrb_cairo_rectangle"
// end of [cairo_rectangle]

(* ****** ****** *)

fun cairo_rel_curve_to
  {l:agz} (
    cr: !cairo_ref l
  , dx1: double, dy1: double
  , dx2: double, dy2: double
  , dx3: double, dy3: double
  ) : void
  = "#atsctrb_cairo_rel_curve_to"
// end of [cairo_rel_curve_to]

fun cairo_rel_line_to
  {l:agz} (cr: !cairo_ref l, dx: double, dy: double): void
  = "#atsctrb_cairo_rel_line_to"
// end of [cairo_rel_line_to]

fun cairo_rel_move_to
  {l:agz} (cr: !cairo_ref l, dx: double, dy: double): void
  = "#atsctrb_cairo_rel_move_to"
// end of [cairo_rel_move_to]

(* ****** ****** *)

fun cairo_path_extents
  {l:agz} (
    cr: !cairo_ref l
  , x1: &double? >> double
  , y1: &double? >> double
  , x2: &double? >> double
  , y2: &double? >> double
  ) : void
  = "#atsctrb_cairo_path_extents"
// end of [cairo_path_extents]

(* ****** ****** *)

//
// patterns for drawing
//

(* ****** ****** *)

// enum type
abst@ype cairo_pattern_type_t = $extype "cairo_pattern_type_t"
macdef CAIRO_PATTERN_TYPE_SOLID =
  $extval (cairo_pattern_type_t, "CAIRO_PATTERN_TYPE_SOLID")
macdef CAIRO_PATTERN_TYPE_SURFACE =
  $extval (cairo_pattern_type_t, "CAIRO_PATTERN_TYPE_SURFACE")
macdef CAIRO_PATTERN_TYPE_LINEAR =
  $extval (cairo_pattern_type_t, "CAIRO_PATTERN_TYPE_LINEAR")
macdef CAIRO_PATTERN_TYPE_RADIAL =
  $extval (cairo_pattern_type_t, "CAIRO_PATTERN_TYPE_RADIAL")

(* ****** ****** *)

fun cairo_pattern_create_rgb
  (red: double, green: double, blue: double): cairo_pattern_ref1
  = "#atsctrb_cairo_pattern_create_rgb"

fun cairo_pattern_create_rgba
  (red: double, green: double, blue: double, alpha: double): cairo_pattern_ref1
  = "#atsctrb_cairo_pattern_create_rgba"

fun cairo_pattern_create_for_surface
  {l:agz} (sf: !cairo_surface_ref l): cairo_pattern_ref1
  = "#atsctrb_cairo_pattern_create_for_surface"
 
fun cairo_pattern_create_linear
  (x0: double, x1: double, x2: double, x3: double): cairo_pattern_ref1
  = "#atsctrb_cairo_pattern_create_linear"

fun cairo_pattern_create_radial (
    cx0: double, cy0: double, rad0: double, cx1: double, cy1: double, rad1: double
  ) : cairo_pattern_ref1 = "#atsctrb_cairo_pattern_create_radial"
// end of [cairo_pattern_create_radial]

(* ****** ****** *)

fun cairo_pattern_status {l:agz} (pat: cairo_pattern_ref l): cairo_status_t
  = "#atsctrb_cairo_pattern_status"

fun cairo_pattern_reference {l:agz}
  (pat: !cairo_pattern_ref l): cairo_pattern_ref l = "#atsctrb_cairo_pattern_reference"
// end of [cairo_pattern_reference]

fun cairo_pattern_destroy
  (pat: cairo_pattern_ref1): void = "#atsctrb_cairo_pattern_destroy"
// end of [cairo_pattern_destroy]

(* ****** ****** *)

fun cairo_pattern_get_type
  {l:agz} (pat: !cairo_pattern_ref l): cairo_pattern_type_t
  = "#atsctrb_cairo_pattern_get_type"

fun cairo_pattern_add_color_stop_rgb {l:agz} (
    pat: !cairo_pattern_ref l
  , offset: double, red: double, green: double, blue: double
  ) : void = "#atsctrb_cairo_pattern_add_color_stop_rgb"
// end of [cairo_pattern_add_color_stop_rgb]

fun cairo_pattern_add_color_stop_rgba {l:agz} (
    pat: !cairo_pattern_ref l
  , offset: double, red: double, green: double, blue: double, alpha: double
  ) : void = "#atsctrb_cairo_pattern_add_color_stop_rgba"
// end of [cairo_pattern_add_color_stop_rgba]

fun cairo_pattern_set_matrix {l:agz}
  (pat: !cairo_pattern_ref l, matrix: &cairo_matrix_t): void
  = "#atsctrb_cairo_pattern_set_matrix"

fun cairo_pattern_get_matrix {l:agz}
  (pat: !cairo_pattern_ref l, matrix: &cairo_matrix_t? >> cairo_matrix_t): void
  = "#atsctrb_cairo_pattern_get_matrix"

(* ****** ****** *)

//
// drawing texts
//

(* ****** ****** *)

// enum type
abst@ype cairo_font_slant_t = $extype "cairo_font_slant_t"
castfn int_of_cairo_font_slant_t (x: cairo_font_slant_t):<> int

macdef CAIRO_FONT_SLANT_NORMAL =
  $extval (cairo_font_slant_t, "CAIRO_FONT_SLANT_NORMAL")

macdef CAIRO_FONT_SLANT_ITALIC =
  $extval (cairo_font_slant_t, "CAIRO_FONT_SLANT_ITALIC")

macdef CAIRO_FONT_SLANT_OBLIQUE =
  $extval (cairo_font_slant_t, "CAIRO_FONT_SLANT_OBLIQUE")

// enum type
abst@ype cairo_font_weight_t = $extype "cairo_font_weight_t"
castfn int_of_cairo_font_weight_t (x: cairo_font_weight_t):<> int

macdef CAIRO_FONT_WEIGHT_NORMAL =
  $extval (cairo_font_weight_t, "CAIRO_FONT_WEIGHT_NORMAL")

macdef CAIRO_FONT_WEIGHT_BOLD =
  $extval (cairo_font_weight_t, "CAIRO_FONT_WEIGHT_BOLD")

(* ****** ****** *)

fun cairo_select_font_face
  {l:agz} (
    cr: !cairo_ref l
  , name: string (* family *)
  , slnt: cairo_font_slant_t
  , wght: cairo_font_weight_t
  ) : void
  = "#atsctrb_cairo_select_font_face"

fun cairo_set_font_size
  {l:agz} (cr: !cairo_ref l, size: double): void
  = "#atsctrb_cairo_set_font_size"

(* ****** ****** *)

fun cairo_get_font_matrix {l:agz}
  (cr: !cairo_ref l, mat: &cairo_matrix_t? >> cairo_matrix_t): void
  = "#atsctrb_cairo_get_font_matrx"

fun cairo_set_font_matrix {l:agz}
  (cr: !cairo_ref l, mat: &cairo_matrix_t): void
  = "#atsctrb_cairo_set_font_matrx"

(* ****** ****** *)

fun cairo_get_font_face
  {l:agz} (cr: !cairo_ref l): cairo_font_face_ref1
  = "#atsctrb_cairo_get_font_face"

fun cairo_set_font_face {l1,l2:agz}
  (cr: !cairo_ref l1, face: !cairo_font_face_ref l2): void
  = "#atsctrb_cairo_set_font_face"

(* ****** ****** *)

(*
// this would be of great inconvenience
abst@ype cairo_glyph_t = $extype "cairo_glyph_t"
abst@ype cairo_cluster_t = $extype "cairo_cluster_t"
*)

typedef cairo_glyph_t =
  $extype_struct "cairo_glyph_t" of { index= ulint, x= double, y= double }
// end of [cairo_glyph_t]

typedef cairo_text_cluster_t =
  $extype_struct "cairo_text_cluster_t" of { num_bytes= int, num_glyphs= int }
// end of [cairo_text_cluster_t]

absviewtype cairo_glyph_arrptr (n:int,l:addr) // = cairo_glyph_t*  
absviewtype cairo_cluster_arrptr (n:int,l:addr) // = cairo_cluster_t*

(*
// this would be of great inconvenience
abst@ype cairo_font_extents_t = $extype "cairo_font_extents_t"
*)
typedef cairo_font_extents_t =
  $extype_struct "cairo_font_extents_t" of {
  ascent= double
, descent= double
, height= double
, max_x_advance= double
, max_y_advance= double
} // end of [cairo_font_extents_t]

(* ****** ****** *)

(*
// this would be of great inconvenience
abst@ype cairo_text_extents_t = $extype "cairo_text_extents_t"
*)
typedef cairo_text_extents_t =
  $extype_struct "cairo_text_extents_t" of {
  x_bearing= double, y_bearing= double
, width= double, height= double
, x_advance= double, y_advance= double
} // end of [cairo_text_extents_t]

(* ****** ****** *)

fun cairo_font_extents
  {l:agz} (
    cr: !cairo_ref l
  , extents: &cairo_font_extents_t? >> cairo_font_extents_t
  ) : void
  = "#atsctrb_cairo_font_extents"

fun cairo_text_extents
  {l:agz} (
    cr: !cairo_ref l, utf8: string
  , extents: &cairo_text_extents_t? >> cairo_text_extents_t
  ) : void
  = "#atsctrb_cairo_text_extents"

fun cairo_glyph_extents
  {l:agz} {n:nat} {la:agz} (
    cr: !cairo_ref l
  , glyphs: !cairo_glyph_arrptr (n, la), n: int n
  , extents: &cairo_text_extents_t? >> cairo_text_extents_t
  ) : void
  = "#atsctrb_cairo_glyph_extents"

(* ****** ****** *)

fun cairo_text_path {l:agz}
  (cr: !cairo_ref l, text: string): void = "#atsctrb_cairo_text_path"
// end of [cairo_text_path]

fun cairo_glyph_path
  {l:agz} {n:nat} {la:agz}
  (cr: !cairo_ref l, glyphs: !cairo_glyph_arrptr (n, la), n: int n)
  : void = "#atsctrb_cairo_glyph_path"
// end of [cairo_glyph_path]

(* ****** ****** *)

fun cairo_show_text {l:agz} (cr: !cairo_ref l, utf8: string): void
  = "#atsctrb_cairo_show_text"

fun cairo_show_glyphs
  {l:agz} {n:nat} {la:agz} (
    cr: !cairo_ref l, glyphs: !cairo_glyph_arrptr (n, la), n: int n
  ) : void = "#atsctrb_cairo_show_glyphs"
// end of [cairo_show_glyphs]

(* ****** ****** *)

fun cairo_toy_font_face_create (
    family: string, s: cairo_font_slant_t, w: cairo_font_weight_t
  ) : cairo_font_face_ref1
  = "#atsctrb_cairo_toy_font_face_create"

fun cairo_toy_font_face_get_family
  {l:agz} (font_face: !cairo_font_face_ref l): string
  = "#atsctrb_cairo_toy_font_face_get_family"

fun cairo_toy_font_face_get_slant
  {l:agz} (font_face: !cairo_font_face_ref l): cairo_font_slant_t
  = "#atsctrb_cairo_toy_font_face_get_slant"

fun cairo_toy_font_face_get_weight
  {l:agz} (font_face: !cairo_font_face_ref l): cairo_font_weight_t
  = "#atsctrb_cairo_toy_font_face_get_weight"

(* ****** ****** *)

fun cairo_glyph_allocate {n:nat}
  (n: int n): [l:agz] cairo_glyph_arrptr (n, l) = "#atsctrb_cairo_glyph_allocate"
// end of [cairo_glyph_allocate]

fun cairo_glyph_free {n:nat} {l:agz} // [l] can be null
  (p_arr: cairo_glyph_arrptr (n, l)): void = "#atsctrb_cairo_glyph_free"
// end of [cairo_glyph_free]

fun cairo_cluster_allocate {n:nat}
  (n: int n): [l:agz] cairo_cluster_arrptr (n, l) = "#atsctrb_cairo_cluster_allocate"
// end of [cairo_cluster_allocate]

fun cairo_cluster_free {n:nat} {l:agz} // [l] can be null
  (p_arr: cairo_cluster_arrptr (n, l)): void = "#atsctrb_cairo_cluster_free"
// end of [cairo_cluster_free]

(* ****** ****** *)

//
// transformations for drawing
//

(* ****** ****** *)

fun cairo_translate {l:agz}
  (cr: !cairo_ref l, x: double, y: double): void
  = "#atsctrb_cairo_translate"

fun cairo_scale {l:agz}
  (cr: !cairo_ref l, sx: double, sy: double): void
  = "#atsctrb_cairo_scale"

fun cairo_rotate {l:agz} (cr: !cairo_ref l, angle: double): void
  = "#atsctrb_cairo_rotate"

fun cairo_transform {l:agz}
  (cr: !cairo_ref l, mat: &cairo_matrix_t): void
  = "#atsctrb_cairo_transform"
  
(* ****** ****** *)

fun cairo_get_matrix
  {l:agz} (
    cr: !cairo_ref l
  , mat: &cairo_matrix_t? >> cairo_matrix_t
  ) : void
  = "#atsctrb_cairo_get_matrix"
  
fun cairo_set_matrix
  {l:agz} (cr: !cairo_ref l, mat: &cairo_matrix_t): void
  = "#atsctrb_cairo_set_matrix"
  
fun cairo_identity_matrix {l:agz} (cr: !cairo_ref l): void
  = "#atsctrb_cairo_identity_matrix"
  
(* ****** ****** *)

fun cairo_user_to_device
  {l:agz} (cr: !cairo_ref l, x: &double, y: &double) : void
  = "#atsctrb_cairo_user_to_device"

fun cairo_user_to_device_distance
  {l:agz} (cr: !cairo_ref l, dx: &double, dy: &double) : void
  = "#atsctrb_cairo_user_to_device_distance"

fun cairo_devide_to_user
  {l:agz} (cr: !cairo_ref l, x: &double, y: &double) : void
  = "#atsctrb_cairo_devide_to_user"

fun cairo_devide_to_user_distance
  {l:agz} (cr: !cairo_ref l, dx: &double, dy: &double) : void
  = "#atsctrb_cairo_devide_to_user_distance"

(* ****** ****** *)

//
// fonts for drawing
//

fun cairo_font_face_reference
  {l:agz} (font_face: !cairo_font_face_ref l): cairo_font_face_ref l
  = "#atsctrb_cairo_font_face_reference"

fun cairo_font_face_destroy
  (font_face: cairo_font_face_ref1): void = "#atsctrb_cairo_font_face_destroy"
// end of [cairo_font_face_destroy]

fun cairo_font_face_status
  {l:agz} (font_face: !cairo_font_face_ref l): cairo_status_t
  = "#atsctrb_cairo_font_face_status"
// end of [cairo_font_face_status]

abst@ype cairo_font_type_t = $extype "cairo_font_type_t"

macdef CAIRO_FONT_TYPE_TOY =
  $extval (cairo_font_type_t, "CAIRO_FONT_TYPE_TOY")
macdef CAIRO_FONT_TYPE_FT =
  $extval (cairo_font_type_t, "CAIRO_FONT_TYPE_FT")
macdef CAIRO_FONT_TYPE_WIN32 =
  $extval (cairo_font_type_t, "CAIRO_FONT_TYPE_WIN32")
macdef CAIRO_FONT_TYPE_QUARTZ =
  $extval (cairo_font_type_t, "CAIRO_FONT_TYPE_QUARTZ")
macdef CAIRO_FONT_TYPE_USER =
  $extval (cairo_font_type_t, "CAIRO_FONT_TYPE_USER")

fun cairo_font_face_get_type
  {l:agz} (font_face: !cairo_font_face_ref l): cairo_font_type_t
  = "#atsctrb_cairo_font_face_get_type"

fun cairo_font_face_get_reference_count
  {l:agz} (font_face: !cairo_font_face_ref l): uint
  = "#atsctrb_cairo_font_face_get_reference_count"

(* ****** ****** *)

//
// scaled fonts
//

absviewtype cairo_scaled_font_ref (l:addr) // cairo_scaled_font_t*
viewtypedef cairo_scaled_font_ref1 = [l:addr | l > null] cairo_scaled_font_ref l

fun cairo_scaled_font_reference
  {l:agz} (font: !cairo_scaled_font_ref l): cairo_scaled_font_ref1
  = "#atsctrb_cairo_scaled_font_reference"
// end of [cairo_scaled_font_reference]

fun cairo_scaled_font_destroy
  (font: cairo_scaled_font_ref1): void = "#atsctrb_cairo_scaled_font_destroy"
// end of [cairo_scaled_font_destroy]

fun cairo_scaled_font_status
  {l:agz} (font: !cairo_scaled_font_ref l): cairo_status_t
  = "#atsctrb_cairo_scaled_font_status"
// end of [cairo_scaled_font_status]

fun cairo_scaled_font_extents {l:agz} (
    font: !cairo_scaled_font_ref l
  , extents: &cairo_font_extents_t? >> cairo_font_extents_t
  ) : void = "#atsctrb_cairo_scaled_font_extents"
// end of [cairo_scaled_font_extents]

fun cairo_scaled_font_text_extents {l:agz} (
    font: !cairo_scaled_font_ref l
  , utf8: string, extents: &cairo_text_extents_t? >> cairo_text_extents_t
  ) : void = "#atsctrb_cairo_scaled_font_text_extents"
// end of [cairo_scaled_font_text_extents]

fun cairo_scaled_font_get_font_face
  {l:agz} (font: !cairo_scaled_font_ref l) : cairo_font_face_ref1
  = "#atsctrb_cairo_scaled_font_get_font_face"
// end of [cairo_scaled_font_get_font_face]

fun cairo_scaled_font_get_font_options
  {l1,l2:agz} (
    font: !cairo_scaled_font_ref l1, options: !cairo_font_options_ptr l2
  ) : void = "#atsctrb_cairo_scaled_font_get_font_options"
// end of [cairo_scaled_font_get_font_options]

fun cairo_scaled_font_get_font_matrix
  {l:agz} (
    font: !cairo_scaled_font_ref l
  , font_matrix: &cairo_matrix_t? >> cairo_matrix_t
  ) : void = "#atsctrb_cairo_scaled_font_get_font_matrix"
// end of [cairo_scaled_font_get_font_matrix]

fun cairo_scaled_font_get_ctm {l:agz} (
    font: !cairo_scaled_font_ref l , ctm: &cairo_matrix_t? >> cairo_matrix_t
  ) : void = "#atsctrb_cairo_scaled_font_get_ctm"
// end of [cairo_scaled_font_get_ctm]

fun cairo_scaled_font_get_scale_matrix {l:agz} (
    font: !cairo_scaled_font_ref l , scale_matrix: &cairo_matrix_t? >> cairo_matrix_t
  ) : void = "#atsctrb_cairo_scaled_font_get_scale_matrix"
// end of [cairo_scaled_font_get_scale_matrix]

fun cairo_scaled_font_get_type
  {l:agz} (font: !cairo_scaled_font_ref l): cairo_font_type_t
  = "#atsctrb_cairo_scaled_font_get_type"
// end of [cairo_scaled_font_get_type]

fun cairo_scaled_font_get_reference_count {l:agz}
  (font: !cairo_scaled_font_ref l): uint = "#atsctrb_cairo_scaled_font_reference_count"
// end of [cairo_scaled_font_reference_count]

(* ****** ****** *)

//
// font options
//

fun cairo_font_options_create
  (): cairo_font_options_ptr1 = "#atsctrb_cairo_font_options_create"
// end of [cairo_font_options_create]

fun cairo_font_options_copy {l:agz}
  (options: !cairo_font_options_ptr l): cairo_font_options_ptr1
  = "#atsctrb_cairo_font_options_copy"

fun cairo_font_options_destroy
  (options: cairo_font_options_ptr1): void = "#atsctrb_cairo_font_options_copy"
// end of [cairo_font_options_destroy]

fun cairo_font_options_status
  {l:agz} (options: !cairo_font_options_ptr l): cairo_status_t
  = "#atsctrb_cairo_font_options_status"
// end of [cairo_font_options_status]

fun cairo_font_options_merge {l1,l2:agz} (
    options: !cairo_font_options_ptr l1, other: !cairo_font_options_ptr l2
  ) : void
  = "#atsctrb_cairo_font_options_merge"

fun cairo_font_options_hash
  {l:agz} (options: !cairo_font_options_ptr l): ulint = "#atsctrb_cairo_font_options_hash"
// end of [cairo_font_options_hash]

fun cairo_font_options_equal {l1,l2:agz} (
    options: !cairo_font_options_ptr l1, other: !cairo_font_options_ptr l2
  ) : bool // cairo_bool_t
  = "#atsctrb_cairo_font_options_equal"
// end of [cairo_font_options_equal]

(* ****** ****** *)

fun cairo_font_options_get_antialias
  {l:agz} (options: !cairo_font_options_ptr l): cairo_antialias_t
  = "#atsctrb_cairo_font_options_get_antialias"
// end of [cairo_font_options_get_antialias]

fun cairo_font_options_set_antialias
  {l:agz} (options: !cairo_font_options_ptr l, antialias: cairo_antialias_t): void
  = "#atsctrb_cairo_font_options_set_antialias"
// end of [cairo_font_options_set_antialias]

(*
** enum
*)
abst@ype cairo_subpixel_order_t = $extype "cairo_subpixel_order_t"

fun cairo_font_options_get_subpixel_order
  {l:agz} (options: !cairo_font_options_ptr l):<> cairo_subpixel_order_t
  = "#atsctrb_cairo_font_options_get_subpixel_order"

fun cairo_font_options_set_subpixel_order {l:agz} (
    options: !cairo_font_options_ptr l, subpixel_order: cairo_subpixel_order_t
  ) : void = "#atsctrb_cairo_font_options_set_subpixel_order"
// end of [cairo_font_options_set_subpixel_order]

(*
** enum
*)
abst@ype cairo_hint_style_t = $extype "cairo_hint_style_t"

fun cairo_font_options_get_hint_style
  {l:agz} (options: !cairo_font_options_ptr l):<> cairo_hint_style_t
  = "#atsctrb_cairo_font_options_get_hint_style"
// end of [cairo_font_options_get_hint_style]

fun cairo_font_options_set_hint_style {l:agz} (
    options: !cairo_font_options_ptr l, hint_style: cairo_hint_style_t
  ) : void = "#atsctrb_cairo_font_options_set_hint_style"
// end of [cairo_font_options_set_hint_style]

(*
** enum
*)
abst@ype cairo_hint_metrics_t = $extype "cairo_hint_metrics_t"

fun cairo_font_options_get_hint_metrics
  {l:agz} (options: !cairo_font_options_ptr l):<> cairo_hint_metrics_t
  = "#atsctrb_cairo_font_options_get_hint_metrics"
// end of [cairo_font_options_get_hint_metrics]

fun cairo_font_options_set_hint_metrics {l:agz} (
    options: cairo_font_options_ptr l, hint_metrics: cairo_hint_metrics_t
  ) : void = "#atsctrb_cairo_font_options_set_hint_metrics"
// end of [cairo_font_options_set_hint_metrics]

(* ****** ****** *)

//
// Support for FreeType Font 
//

(* ****** ****** *)

(*
#define CAIRO_HAS_FT_FONT
*)

absviewtype FT_Face // boxed object
absviewtype FcPattern_ptr // FcPattern*

fun cairo_ft_font_face_create_for_ft_face
  (face: FT_Face, load_flags: int): cairo_font_face_ref1
  = "#atsctrb_cairo_ft_font_face_create_for_ft_face"
// end of [cairo_ft_font_face_create_for_ft_face]

fun cairo_ft_font_face_create_for_pattern
  (pattern: FcPattern_ptr): cairo_font_face_ref1
  = "#atsctrb_cairo_ft_font_face_create_for_pattern"
// end of [cairo_ft_font_face_create_for_pattern]

fun cairo_ft_font_options_substitute
  {l:agz} (options: !cairo_font_options_ptr l, pattern: FcPattern_ptr):<> void
  = "#atsctrb_cairo_ft_font_options_substitute"
// end of [cairo_ft_font_options_substitute]

absview scaled_font_lock_face_v (l:addr)

fun cairo_ft_scaled_font_lock_face {l:agz}
  (scaled_font: !cairo_scaled_font_ref l):<> (scaled_font_lock_face_v l | FT_Face)
  = "#atsctrb_cairo_ft_scaled_font_lock_face"
// end of [cairo_ft_scaled_font_lock_face]

fun cairo_ft_scaled_font_unlock_face {l:agz}
  (pf: scaled_font_lock_face_v l | scaled_font: !cairo_scaled_font_ref l):<> void
  = "#atsctrb_cairo_ft_scaled_font_unlock_face"
// end of [cairo_ft_scaled_font_unlock_face]

(* ****** ****** *)

//
// surfaces for drawing
//

(* ****** ****** *)

fun cairo_surface_create_similar {l:agz} (
    sf: !cairo_surface_ref l, content: cairo_content_t, width: int, height: int
  ) : cairo_surface_ref1 = "#atsctrb_cairo_surface_create_similar"
// end of [cairo_surface_create_similar]

fun cairo_surface_reference {l:agz}
  (sf: !cairo_surface_ref l): cairo_surface_ref l = "#atsctrb_cairo_surface_reference"
// end of [cairo_surface_reference]

fun cairo_surface_destroy
  (sf: cairo_surface_ref1): void = "#atsctrb_cairo_surface_destroy"
// end of [cairo_surface_destroy]

fun cairo_surface_status {l:agz}
  (sf: !cairo_surface_ref l): cairo_status_t = "#atsctrb_cairo_surface_status"
// end of [cairo_surface_status]

fun cairo_surface_finish {l:agz}
  (sf: !cairo_surface_ref l): void = "#atsctrb_cairo_surface_finish"
// end of [cairo_surface_finish]

fun cairo_surface_flush {l:agz}
  (sf: !cairo_surface_ref l): void = "#atsctrb_cairo_surface_flush"
// end of [cairo_surface_flush]

fun cairo_surface_get_font_options {l1,l2:agz}
  (sf: !cairo_surface_ref l1, options: !cairo_font_options_ptr l2): void
  = "#atsctrb_cairo_surface_get_font_options"
// end of [cairo_surface_get_font_options]

fun cairo_surface_get_content {l:agz}
  (sf: !cairo_surface_ref l): cairo_content_t
  = "#atsctrb_cairo_surface_get_content"
// end of [cairo_surface_get_content]

fun cairo_surface_mark_dirty {l:agz}
  (sf: !cairo_surface_ref l): void = "#atsctrb_cairo_surface_mark_dirty"
// end of [cairo_surface_mark_dirty]

fun cairo_surface_mark_dirty_rectangle {l:agz}
  (sf: !cairo_surface_ref l, x: int, y: int, width: int, height: int): void
  = "#atsctrb_cairo_surface_mark_dirty"
// end of [cairo_surface_mark_dirty_rectangle]

fun cairo_get_device_offset {l:agz} (
    sf: !cairo_surface_ref l, x_ofs: &double? >> double, y_ofs: &double? >> double
  ) : void = "#atsctrb_cairo_get_device_offset"
// end of [cairo_get_device_offset]

fun cairo_set_device_offset {l:agz}
  (sf: !cairo_surface_ref l, x_ofs: double, y_ofs: double): void
  = "#atsctrb_cairo_set_device_offset"
// end of [cairo_set_device_offset]

// enum type
abstype cairo_surface_type_t = $extype "cairo_surface_type_t"

macdef CAIRO_SURFACE_TYPE_IMAGE =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_IMAGE")

macdef CAIRO_SURFACE_TYPE_PDF =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_PDF")

macdef CAIRO_SURFACE_TYPE_PS =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_PS")

macdef CAIRO_SURFACE_TYPE_XLIB =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_XLIB")

macdef CAIRO_SURFACE_TYPE_XCB =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_XCB")

macdef CAIRO_SURFACE_TYPE_GLITZ =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_GLITZ")

macdef CAIRO_SURFACE_TYPE_QUARTZ =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_QUARTZ")
macdef CAIRO_SURFACE_TYPE_QUARTZ_IMAGE =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_QUARTZ_IMAGE")

macdef CAIRO_SURFACE_TYPE_WIN32 =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_WIN32")
macdef CAIRO_SURFACE_TYPE_WIN32_PRINTING =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_WIN32_PRINTING")

macdef CAIRO_SURFACE_TYPE_BEOS =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_BEOS")

macdef CAIRO_SURFACE_TYPE_DIRECTFB =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_DIRECTFB")

macdef CAIRO_SURFACE_TYPE_SVG =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_SVG")

macdef CAIRO_SURFACE_TYPE_OS2 =
  $extval (cairo_surface_type_t, "CAIRO_SURFACE_TYPE_OS2")

fun cairo_surface_get_type {l:agz}
  (sf: !cairo_surface_ref l): cairo_surface_type_t = "#atsctrb_cairo_surface_get_type"
// end of [cairo_surface_get_type]

fun cairo_surface_get_reference_count {l:agz}
  (sf: !cairo_surface_ref l): int = "#atsctrb_cairo_surface_get_reference_count"
// end of [cairo_surface_get_reference_count]

fun cairo_surface_copy_page
  {l:agz} (sf: !cairo_surface_ref l): void = "#atsctrb_cairo_surface_copy_page"
// end of [cairo_surface_copy_page]

fun cairo_surface_show_page
  {l:agz} (sf: !cairo_surface_ref l): void = "#atsctrb_cairo_surface_show_page"
// end of [cairo_surface_show_page]

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
  = "#atsctrb_cairo_format_stride_for_width"

fun cairo_image_surface_create
  (format: cairo_format_t, width: int, height: int) : cairo_surface_ref1
  = "#atsctrb_cairo_image_surface_create"
// end of [cairo_image_surface_create]

//
// this one is unsafe but ...
//
fun cairo_image_surface_create_for_data (
    data: ptr // uchar*
  , format: cairo_format_t
  , width: int, height: int, stride: int
  ) : cairo_surface_ref1
  = "#atsctrb_cairo_image_surface_create_for_data"

fun cairo_image_surface_get_data
  {l:agz} (sf: !cairo_surface_ref l): Ptr // uchar*
  = "#atsctrb_cairo_image_surface_get_data"

fun cairo_image_surface_get_format
  {l:agz} (sf: !cairo_surface_ref l): cairo_format_t
  = "#atsctrb_cairo_image_surface_get_format"

fun cairo_image_surface_get_width
  {l:agz} (sf: !cairo_surface_ref l): Nat = "#atsctrb_cairo_image_surface_get_width"
// end of [cairo_image_surface_get_width]

fun cairo_image_surface_get_height
  {l:agz} (sf: !cairo_surface_ref l): Nat = "#atsctrb_cairo_image_surface_get_height"
// end of [cairo_image_surface_get_height]

fun cairo_image_surface_get_stride
  {l:agz} (sf: !cairo_surface_ref l): Nat = "#atsctrb_cairo_image_surface_get_stride"
// end of [cairo_image_surface_get_stride]

(* ****** ****** *)

//
// PNG support
//

fun cairo_image_surface_create_from_png
  (filename: string): cairo_surface_ref1
  = "#atsctrb_cairo_image_surface_create_from_png"
// end of [cairo_image_surface_create_from_png]

fun cairo_image_surface_create_from_png_stream
  {v:view} {vt:viewtype} (
    pf: !v
  | read_func: (!v | !vt, string, uint) -<fun1> cairo_status_t
  , env: !vt
  ) : cairo_surface_ref1
  = "#atsctrb_cairo_image_surface_create_from_png"

fun cairo_surface_write_to_png
  {l:agz} (sf: !cairo_surface_ref l, filename: string): cairo_status_t
  = "#atsctrb_cairo_surface_write_to_png"
// end of [cairo_surface_write_to_png]

fun cairo_surface_write_to_png_stream
  {v:view} {vt:viewtype} {l:agz} (
    pf: !v
  | sf: !cairo_surface_ref l
  , write_func: (!v | !vt, string, uint) -<fun1> cairo_status_t
  , env: !vt
  ) : cairo_status_t
  = "#atsctrb_cairo_surface_write_to_png_stream"
// end of [cairo_surface_write_to_png_stream]

(* ****** ****** *)

//
// PDF surface
//

(*
#define CAIRO_HAS_PDF_SURFACE
*)

fun cairo_pdf_surface_create (
    filename: string, width_in_points: double, height_in_points: double
  ) : cairo_surface_ref1
  = "#atsctrb_cairo_pdf_surface_create"
// end of [cairo_pdf_surface_create]

fun cairo_pdf_surface_create_null (
    width_in_points: double, height_in_points: double
  ) : cairo_surface_ref1
  = "atsctrb_cairo_pdf_surface_create_null" // function!
// end of [cairo_pdf_surface_create_null]

(*
** note that [pf] and [env] can be freed only after the
** returned surface is destroyed by a call to[cairo_surface_destroy]
*)
fun cairo_pdf_surface_create_for_stream
  {v:view} {vt:viewtype} (
    pf: !v
  | write_func: (!v | !vt, string, uint) -<fun1> cairo_status_t
  , env: !vt
  , width_in_points: double
  , height_in_points: double
  ) : cairo_surface_ref1
  = "#atsctrb_cairo_pdf_surface_create_for_stream"
// end of [cairo_pdf_surface_create_for_stream]

fun cairo_pdf_surface_set_size {l:agz} (
    sf: !cairo_surface_ref l, width_in_points: double, height_in_points: double
  ) : void = "#atsctrb_cairo_pdf_surface_set_size"
// end of [cairo_pdf_surface_set_size]

(* ****** ****** *)

//
// PS surface
//

(*
#define CAIRO_HAS_PS_SURFACE
*)

fun cairo_ps_surface_create (
    filename: string, width_in_points: double, height_in_points: double
  ) : cairo_surface_ref1
  = "#atsctrb_cairo_ps_surface_create"
// end of [cairo_ps_surface_create]

fun cairo_ps_surface_create_null (
    width_in_points: double, height_in_points: double
  ) : cairo_surface_ref1
  = "atsctrb_cairo_ps_surface_create_null" // function
// end of [cairo_ps_surface_create_null]

(*
** note that [pf] and [env] can be freed only after the
** returned surface is destroyed by a call to[cairo_surface_destroy]
*)
fun cairo_ps_surface_create_for_stream
  {v:view} {vt:viewtype} (
    pf: !v
  | write_func: (!v | !vt, string, uint) -<fun1> cairo_status_t
  , env: !vt
  , width_in_points: double
  , height_in_points: double
  ) : cairo_surface_ref1
  = "#atsctrb_cairo_ps_surface_create_for_stream"
// end of [cairo_ps_surface_create_for_stream]

(*
// enum
abst@ype cairo_ps_level_t = $extype "cairo_ps_level_t"

macdef CAIRO_PS_LEVEL_2 =
  $extval (cairo_ps_level_t, "CAIRO_PS_LEVEL_2")
macdef CAIRO_PS_LEVEL_3 =
  $extval (cairo_ps_level_t, "CAIRO_PS_LEVEL_3")

(*
void cairo_ps_get_levels
  (cairo_ps_level_t const **levels, int *num_levels);
*)
fun cairo_ps_get_levels
  (num_levels: &int? >> int n): #[n:nat] array (cairo_ps_level_t, n)
  = "#atsctrb_cairo_ps_get_levels"
// end of [cairo_ps_get_levels]

// a null string is returned if [level] is invalid
fun cairo_ps_level_to_string (level: cairo_ps_level_t): Stropt
*)

fun cairo_ps_surface_set_size
  {l:agz} (
    sf: !cairo_surface_ref l
  , width_in_points: double, height_in_points: double
  ) : void = "#atsctrb_cairo_ps_surface_set_size"
// end of [cairo_ps_surface_set_size]

fun cairo_ps_surface_dsc_begin_setup
  {l:agz} (sf: !cairo_surface_ref l) : void
  = "#atsctrb_cairo_ps_surface_dsc_begin_setup"
// end of [cairo_ps_surface_dsc_begin_setup]

fun cairo_ps_surface_dsc_begin_page_setup
  {l:agz} (sf: !cairo_surface_ref l) : void
  = "#atsctrb_cairo_ps_surface_dsc_begin_page_setup"
// end of [cairo_ps_surface_dsc_begin_page_setup]

fun cairo_ps_surface_dsc_comment
  {l:agz} (sf: !cairo_surface_ref l, comment: string): void
  = "#atsctrb_cairo_ps_surface_dsc_comment"
// end of [cairo_ps_surface_dsc_comment]

(* ****** ****** *)

(*
#define CAIRO_HAS_SVG_SURFACE
*)
fun cairo_svg_surface_create (
    filename: string
  , width_in_points: double, height_in_points: double
  ) : cairo_surface_ref1
  = "#atsctrb_cairo_svg_surface_create"
// end of [cairo_svg_surface_create]

(*
** note that [pf] and [env] can be freed only after the
** returned surface is destroyed by a call to[cairo_surface_destroy]
*)
fun cairo_svg_surface_create_for_stream
  {v:view} {vt:viewtype} (
    pf: !v
  | write_func: (!v | !vt, string, uint) -<fun1> cairo_status_t
  , env: !vt
  , width_in_points: double
  , height_in_points: double
  ) : cairo_surface_ref1
  = "#atsctrb_cairo_svg_surface_create_for_stream"
// end of [cairo_svg_surface_create_for_stream]

// enum type
abst@ype cairo_svg_version_t = $extype "cairo_svg_version_t"

fun cairo_svg_surface_restrict_to_version
  {l:agz} (cr: !cairo_ref l, version: cairo_svg_version_t): void
  = "#atsctrb_cairo_svg_surface_restrict_to_version"

fun cairo_svg_get_versions
  (n: &int? >> int n): #[n:nat] array (cairo_svg_version_t, n)
  = "atsctrb_cairo_svg_get_versions" // this is a function!

fun cairo_svg_version_to_string
  (version: cairo_svg_version_t): string = "#atsctrb_cairo_svg_version_to_string"
// end of [cairo_svg_version_to_string]

(* ****** ****** *)

//
// Quartz surface
//

(*
#define CAIRO_HAS_QUARTZ_SURFACE
*)

fun cairo_quartz_surface_create
  (format: cairo_format_t, width: uint, height: uint): cairo_surface_ref1
  = "#atsctrb_cairo_quartz_surface_create"

(*
** HX (2010-01-9):
** this type should probably be linear; however I do not really know
** how it can be properly handled as I have never used it.
*)
abstype CGContextRef = $extype "CGContextRef"

fun cairo_quartz_surface_create_for_cg_context
  (cgContext: CGContextRef, width: uint, height: uint): cairo_surface_ref1
  = "#atsctrb_cairo_quartz_surface_create_for_cg_context"
// end of [cairo_quartz_surface_create_for_cg_context]

fun cairo_quartz_surface_get_cg_context
  {l:agz} (surface: !cairo_surface_ref l): CGContextRef
  = "#atsctrb_cairo_quartz_surface_get_cg_context"
// end of [cairo_quartz_surface_get_cg_context]

(* ****** ****** *)

//
// Xlib surface
//

(*
#define CAIRO_HAS_XLIB_SURFACE
*)

staload X = "contrib/X11/SATS/X.sats"
staload Xlib = "contrib/X11/SATS/Xlib.sats"
stadef Drawable = $X.Drawable
stadef Pixmap = $X.Pixmap
stadef Display_ptr = $Xlib.Display_ptr
stadef Screen_ptr = $Xlib.Screen_ptr
stadef Visual_ptr = $Xlib.Visual_ptr

fun cairo_xlib_surface_create {l1,l2:agz} (
    dpy: !Display_ptr l1
  , drw: Drawable, visual: !Visual_ptr l2, width: int, height: int
  ) : cairo_surface_ref1
  = "#atsctrb_cairo_xlib_surface_create"
// end of [cairo_xlib_surface_create]
  
fun cairo_xlib_surface_create_for_bitmap {l1,l2:agz} (
    dpy: !Display_ptr l1
  , bitmap: Pixmap, scr: !Screen_ptr l2, width: int, height: int
  ) : cairo_surface_ref1
  = "#atsctrb_cairo_xlib_surface_create_for_bitmap"
// end of [cairo_xlib_surface_create_for_bitmap]

fun cairo_xlib_surface_set_size {l:agz}
  (surface: !cairo_surface_ref l, width: int, height: int): void
  = "#atsctrb_cairo_xlib_surface_set_size"
// end of [cairo_xlib_surface_set_size]

fun cairo_xlib_surface_set_drawable {l:agz} (
    surface: !cairo_surface_ref l, drw: Drawable, width: int, height: int
  ) : void = "#atsctrb_cairo_xlib_surface_set_drawable"
// end of [cairo_xlib_surface_set_drawable]

fun cairo_xlib_surface_get_drawable
  {l:agz} (surface: !cairo_surface_ref l): Drawable
  = "#atsctrb_cairo_xlib_surface_get_drawable"
// end of [cairo_xlib_surface_get_drawable]

fun cairo_xlib_surface_get_display
  {l1:agz} (surface: !cairo_surface_ref l1)
  : [l2:agz] (
    minus (cairo_surface_ref l1, Display_ptr l2) | Display_ptr l2
  ) = "#atsctrb_cairo_xlib_surface_get_display"
// end of [cairo_xlib_surface_get_display]

fun cairo_xlib_surface_get_screen
  {l1:agz} (surface: !cairo_surface_ref l1)
  : [l2:agz] (
    minus (cairo_surface_ref l1, Screen_ptr l2) | Screen_ptr l2
  ) = "#atsctrb_cairo_xlib_surface_get_screen"
// end of [cairo_xlib_surface_get_screen]

fun cairo_xlib_surface_get_visual
  {l1:agz} (surface: !cairo_surface_ref l1)
  : [l2:agz] (
    minus (cairo_surface_ref l1, Visual_ptr l2) | Visual_ptr l2
  ) = "#atsctrb_cairo_xlib_surface_get_visual"
// end of [cairo_xlib_surface_get_visual]

fun cairo_xlib_surface_get_width {l:agz}
  (surface: !cairo_surface_ref l): int = "#atsctrb_cairo_xlib_surface_get_width"
// end of [cairo_xlib_surface_get_width]

fun cairo_xlib_surface_get_height {l:agz}
  (surface: !cairo_surface_ref l): int = "#atsctrb_cairo_xlib_surface_get_height"
// end of [cairo_xlib_surface_get_height]

fun cairo_xlib_surface_get_depth {l:agz}
  (surface: !cairo_surface_ref l): int = "#atsctrb_cairo_xlib_surface_get_depth"
// end of [cairo_xlib_surface_get_depth]

(* ****** ****** *)

//
// utilities for drawing
//

(* ****** ****** *)

//
// generic matrix operations
//

(* ****** ****** *)

fun cairo_matrix_init (
    matrix: &cairo_matrix_t? >> cairo_matrix_t
  , xx: double, yx: double, xy: double, yy: double
  , x0: double, y0: double
  ) : void = "#atsctrb_cairo_matrix_init"
// end of [cairo_matrix_init]

fun cairo_matrix_init_identity
  (matrix: &cairo_matrix_t? >> cairo_matrix_t): void
  = "#atsctrb_cairo_matrix_init_identity"
// end of [cairo_matrix_init_identity]

fun cairo_matrix_init_translate (
    matrix: &cairo_matrix_t? >> cairo_matrix_t, tx: double, ty: double
  ) : void = "#atsctrb_cairo_matrix_init_translate"
// end of [cairo_matrix_init_translate]

fun cairo_matrix_init_scale (
    matrix: &cairo_matrix_t? >> cairo_matrix_t, sx: double, sy: double
  ) : void = "#atsctrb_cairo_matrix_init_scale"
// end of [cairo_matrix_init_scale]

fun cairo_matrix_init_rotate (
    matrix: &cairo_matrix_t? >> cairo_matrix_t, angle: double
  ) : void = "#atsctrb_cairo_matrix_init_rotate"
// end of [cairo_matrix_init_rotate]

(* ****** ****** *)

fun cairo_matrix_translate (
    matrix: &cairo_matrix_t >> cairo_matrix_t, tx: double, ty: double
  ) : void = "#atsctrb_cairo_matrix_translate"
// end of [cairo_matrix_translate]

fun cairo_matrix_scale (
    matrix: &cairo_matrix_t >> cairo_matrix_t, sx: double, sy: double
  ) : void = "#atsctrb_cairo_matrix_scale"
// end of [cairo_matrix_scale]

fun cairo_matrix_rotate (
    matrix: &cairo_matrix_t >> cairo_matrix_t, angle: double
  ) : void = "#atsctrb_cairo_matrix_rotate"
// end of [cairo_matrix_rotate]

(* ****** ****** *)

fun cairo_matrix_invert
  (matrix: &cairo_matrix_t >> cairo_matrix_t): cairo_status_t
  = "#atsctrb_cairo_matrix_invert"
// end of [cairo_matrix_invert]

fun cairo_matrix_multiply (
    result: &cairo_matrix_t? >> cairo_matrix_t
  , amatrix: &cairo_matrix_t (*read*)
  , bmatrix: &cairo_matrix_t (*read*)
  ) : void = "#atsctrb_cairo_matrix_multiply"
// end of [cairo_matrix_multiply]

fun cairo_matrix_transform_distance (
    matrix: &cairo_matrix_t (*read*), dx: &double, dy: &double
  ) : void = "#atsctrb_cairo_matrix_transform_distance"
// end of [cairo_matrix_transform_distance]

fun cairo_matrix_transform_point (
    matrix: &cairo_matrix_t (*read*), x: &double, y: &double
  ) : void = "#atsctrb_cairo_matrix_transform_point"
// end of [cairo_matrix_transform_point]

(* ****** ****** *)

//
// error handling
//

// all error strings are statically allocated
fun cairo_status_to_string
  (status: cairo_status_t):<> string = "#atsctrb_cairo_status_to_string"
// end of [cairo_status_to_string]

fun cairo_debug_reset_static_data
  (): void = "#atsctrb_cairo_debug_reset_static_data"
// end of [cairo_debug_reset_static_data]

(* ****** ****** *)

//
// cairo version macros and functions
//

macdef CAIRO_VERSION = $extval (int, "CAIRO_VERSION")
macdef CAIRO_VERSION_MAJOR = $extval (int, "CAIRO_VERSION_MAJOR")
macdef CAIRO_VERSION_MINOR = $extval (int, "CAIRO_VERSION_MINOR")
macdef CAIRO_VERSION_MICRO = $extval (int, "CAIRO_VERSION_MICRO")
macdef CAIRO_VERSION_STRING = $extval (string, "CAIRO_VERSION_STRING")

fun CAIRO_VERSION_ENCODE
  (major: int, minor: int, micro: int): int = "#CAIRO_VERSION_ENCODE"
// end of [CAIRO_VERSION_ENCODE]

fun CAIRO_VERSION_STRINGIZE
  (major: int, minor: int, micro: int): string = "#CAIRO_VERSION_STRINGIZE"
// end of [CAIRO_VERSION_STRINGIZE]

fun cairo_version (): int = "#atsctrb_cairo_version"
fun cairo_version_string (): string = "atsctrb_cairo_version_string" // function!
  
(* ****** ****** *)

(* end of [cairo.sats] *)
