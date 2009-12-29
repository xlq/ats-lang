/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/*                              Hongwei Xi                             */
/*                                                                     */
/***********************************************************************/

/*
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
*/

/* ****** ****** */

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: December, 2009

/* ****** ****** */

#ifndef ATSCTRB_CAIRO_CAIRO_CATS
#define ATSCTRB_CAIRO_CAIRO_CATS

/* ****** ****** */

#include <cairo-features.h>
#include <cairo.h>
#include <cairo-pdf.h>
#include <cairo-ps.h>

/* ****** ****** */

typedef ats_ref_type ats_cairo_ref ;
typedef ats_ref_type ats_cairo_surface_ref ;
typedef ats_ref_type ats_cairo_pattern_ref ;
typedef ats_ref_type ats_cairo_font_face_ref ;

typedef cairo_status_t ats_cairo_status_type ;
typedef cairo_operator_t ats_cairo_operator_type ;
typedef cairo_format_t ats_cairo_format_type ;
typedef cairo_font_slant_t ats_cairo_font_slant_type ;
typedef cairo_font_weight_t ats_cairo_font_weight_type ;

/* ****** ****** */

static inline
ats_bool_type
atsctrb_eq_cairo_status_cairo_status (
  ats_cairo_status_type x1, ats_cairo_status_type x2
) {
  return (x1 == x2 ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_eq_cairo_status_cairo_status]

/* ****** ****** */

//
// contexts for drawing
//

static inline
ats_cairo_ref
atsctrb_cairo_create
  (ats_cairo_surface_ref sf) {
  return cairo_create((cairo_surface_t*)sf) ;
}

static inline
ats_cairo_ref
atsctrb_cairo_reference
  (ats_cairo_ref cr) {
  return cairo_reference((cairo_t*)cr) ;
}

static inline
ats_void_type
atsctrb_cairo_destroy
  (ats_cairo_ref cr) {
  cairo_destroy((cairo_t*)cr) ; return ;
}

/* ****** ****** */

static inline
ats_cairo_status_type
atsctrb_cairo_status
  (ats_cairo_ref cr) {
  return cairo_status((cairo_t*)cr) ;
}

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_save
  (ats_cairo_ref cr) {
  cairo_save((cairo_t*)cr) ; return ;
}

static inline
ats_void_type
atsctrb_cairo_restore
  (ats_cairo_ref cr) {
  cairo_restore((cairo_t*)cr) ; return ;
}

/* ****** ****** */

static inline
ats_cairo_surface_ref
atsctrb_cairo_get_target
  (ats_cairo_ref cr) {
  return cairo_get_target((cairo_t*)cr) ;
}

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_push_group
  (ats_cairo_ref cr) {
  cairo_push_group((cairo_t*)cr) ; return ;
}

typedef cairo_content_t ats_cairo_content_type ;

static inline
ats_void_type
atsctrb_cairo_push_group_with_content (
  ats_cairo_ref cr, ats_cairo_content_type content
) {
  cairo_push_group_with_content((cairo_t*)cr, content) ; return ;
} // end of [atsctrb_cairo_push_group_with_content]

static inline
ats_cairo_pattern_ref
atsctrb_cairo_pop_group
  (ats_cairo_ref cr) {
  return cairo_pop_group((cairo_t*)cr) ;
}

static inline
ats_void_type
atsctrb_cairo_pop_group_to_source
  (ats_cairo_ref cr) {
  cairo_pop_group_to_source((cairo_t*)cr) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_set_source_rgb (
  ats_cairo_ref cr
, ats_double_type r
, ats_double_type g
, ats_double_type b
) {
  cairo_set_source_rgb((cairo_t*)cr, r, g, b) ; return ;
} /* end of [atsctrb_cairo_set_source_rgb] */

static inline
ats_void_type
atsctrb_cairo_set_source_rgba (
  ats_cairo_ref cr
, ats_double_type r
, ats_double_type g
, ats_double_type b
, ats_double_type a
) {
  cairo_set_source_rgba((cairo_t*)cr, r, g, b, a) ; return ;
} /* end of [atsctrb_cairo_set_source_rgba] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_set_source (
  ats_cairo_ref cr, ats_cairo_pattern_ref pat
) {
  cairo_set_source((cairo_t*)cr, (cairo_pattern_t*)pat) ;
  return ;
} /* end of [atsctrb_cairo_set_source] */

static inline
ats_void_type
atsctrb_cairo_set_source_surface (
  ats_cairo_ref cr
, ats_cairo_surface_ref sf
, ats_double_type x, ats_double_type y
) {
  cairo_set_source_surface(
    (cairo_t*)cr, (cairo_surface_t*)sf, x, y
  ) ; return ;
} /* end of [atsctrb_cairo_set_source_surface] */

/* ****** ****** */

typedef cairo_antialias_t ats_cairo_antialias_type ;

static inline
ats_cairo_antialias_type
atsctrb_cairo_get_antialias
  (ats_cairo_ref cr) {
  return cairo_get_antialias((cairo_t*)cr) ;
} /* end of [atsctrb_cairo_get_antialias] */

static inline
ats_void_type
atsctrb_cairo_set_antialias (
  ats_cairo_ref cr, ats_cairo_antialias_type rule
) {
  cairo_set_antialias((cairo_t*)cr, rule) ; return ;
} /* end of [atsctrb_cairo_set_antialias] */

/* ****** ****** */

static inline
ats_int_type
atsctrb_cairo_get_dash_count
  (ats_cairo_ref cr) {
  return cairo_get_dash_count ((cairo_t*)cr) ; 
} // end of [atsctrb_cairo_get_dash_count]

static inline
ats_int_type
atsctrb_cairo_get_dash (
  ats_cairo_ref cr
, ats_ptr_type dashes, ats_int_type n
, ats_ptr_type offset
) {
  int n1 = cairo_get_dash_count((cairo_t*)cr) ;
  if (n1 <= n) {
    cairo_get_dash((cairo_t*)cr, (double*)dashes, (double*)offset) ;
  } else {
    cairo_get_dash((cairo_t*)cr, (double*)0, (double*)offset) ;
  } // end of [if]
  return n1 ;
} // end of [atsctrb_cairo_get_dash]

static inline
ats_int_type
atsctrb_cairo_set_dash (
  ats_cairo_ref cr
, ats_ptr_type dashes, ats_int_type n
, ats_double_type offset
) {
  cairo_set_dash((cairo_t*)cr, (double*)dashes, n, offset) ;
  return ;
} // end of [atsctrb_cairo_set_dash]

/* ****** ****** */

typedef cairo_fill_rule_t ats_cairo_fill_rule_type ;

static inline
ats_cairo_fill_rule_type
atsctrb_cairo_get_fill_rule
  (ats_cairo_ref cr) {
  return cairo_get_fill_rule((cairo_t*)cr) ;
} /* end of [atsctrb_cairo_get_fill_rule] */

static inline
ats_void_type
atsctrb_cairo_set_fill_rule (
  ats_cairo_ref cr, ats_cairo_fill_rule_type rule
) {
  cairo_set_fill_rule((cairo_t*)cr, rule) ; return ;
} /* end of [atsctrb_cairo_set_fill_rule] */

/* ****** ****** */

typedef cairo_line_cap_t ats_cairo_line_cap_type ;

static inline
ats_cairo_line_cap_type
atsctrb_cairo_get_line_cap
  (ats_cairo_ref cr) {
  return cairo_get_line_cap((cairo_t*)cr) ;
} /* end of [atsctrb_cairo_get_line_cap] */

static inline
ats_void_type
atsctrb_cairo_set_line_cap (
  ats_cairo_ref cr, ats_cairo_line_cap_type rule
) {
  cairo_set_line_cap((cairo_t*)cr, rule) ; return ;
} /* end of [atsctrb_cairo_set_line_cap] */

/* ****** ****** */

typedef cairo_line_join_t ats_cairo_line_join_type ;

static inline
ats_cairo_line_join_type
atsctrb_cairo_get_line_join
  (ats_cairo_ref cr) {
  return cairo_get_line_join((cairo_t*)cr) ;
} /* end of [atsctrb_cairo_get_line_join] */

static inline
ats_void_type
atsctrb_cairo_set_line_join (
  ats_cairo_ref cr, ats_cairo_line_join_type rule
) {
  cairo_set_line_join((cairo_t*)cr, rule) ; return ;
} /* end of [atsctrb_cairo_set_line_join] */

/* ****** ****** */

static inline
ats_double_type
atsctrb_cairo_get_line_width
  (ats_cairo_ref cr) {
  return cairo_get_line_width((cairo_t*)cr) ;
} /* end of [atsctrb_cairo_get_line_width] */

static inline
ats_void_type
atsctrb_cairo_set_line_width (
  ats_cairo_ref cr, ats_double_type width
) {
  cairo_set_line_width((cairo_t*)cr, width) ; return ;
} /* end of [atsctrb_cairo_set_line_width] */

/* ****** ****** */

static inline
ats_double_type
atsctrb_cairo_get_miter_limit
  (ats_cairo_ref cr) {
  return cairo_get_miter_limit((cairo_t*)cr) ;
} /* end of [atsctrb_cairo_get_miter_limit] */

static inline
ats_void_type
atsctrb_cairo_set_miter_limit (
  ats_cairo_ref cr, ats_double_type limit
) {
  cairo_set_miter_limit((cairo_t*)cr, limit) ; return ;
} /* end of [atsctrb_cairo_set_miter_limit] */

/* ****** ****** */

static inline
ats_cairo_operator_type
atsctrb_cairo_get_operator
  (ats_cairo_ref cr) {
  return cairo_get_operator((cairo_t*)cr) ;
} /* end of [atsctrb_cairo_get_operator] */

static inline
ats_void_type
atsctrb_cairo_set_operator (
  ats_cairo_ref cr, ats_cairo_operator_type rule
) {
  cairo_set_operator((cairo_t*)cr, rule) ; return ;
} /* end of [atsctrb_cairo_set_operator] */

/* ****** ****** */

static inline
ats_double_type
atsctrb_cairo_get_tolerance
  (ats_cairo_ref cr) {
  return cairo_get_tolerance((cairo_t*)cr) ;
} /* end of [atsctrb_cairo_get_tolerance] */

static inline
ats_void_type
atsctrb_cairo_set_tolerance (
  ats_cairo_ref cr, ats_double_type tolerance
) {
  cairo_set_tolerance((cairo_t*)cr, tolerance) ; return ;
} /* end of [atsctrb_cairo_set_tolerance] */

/* ****** ****** */

#if (CAIRO_VERSION >= CAIRO_VERSION_ENCODE (1, 4, 0))

static inline
ats_void_type
atsctrb_cairo_rectangle_list_destroy
  (ats_ref_type lst) {
  cairo_rectangle_list_destroy((cairo_rectangle_list_t*)lst) ;
  return ;
} // end of [cairo_rectangle_list_destroy]

static inline
ats_ref_type
atsctrb_cairo_clip_rectangle_list)
  (ats_cairo_ref cr)
  return cairo_clip_rectangle_list((cairo_t*)cr) ;
} // end of [cairo_clip_rectangle_list]

#endif // end of [#if (CAIRO_VERSION >= 1.4.0)]

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_clip (
  ats_cairo_ref cr
) {
  cairo_clip((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_clip] */

static inline
ats_void_type
atsctrb_cairo_clip_preserve (
  ats_cairo_ref cr
) {
  cairo_clip_preserve((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_clip_preserve] */

static inline
ats_void_type
atsctrb_cairo_clip_extents (
  ats_cairo_ref cr
, ats_ref_type x1, ats_ref_type y1
, ats_ref_type x2, ats_ref_type y2
) {
  cairo_clip_extents(
    (cairo_t*)cr, (double*)x1, (double*)y1, (double*)x2, (double*)y2
  ) ; return ;
} /* end of [atsctrb_cairo_clip_extents] */

static inline
ats_void_type
atsctrb_cairo_reset_clip
  (ats_cairo_ref cr) {
  cairo_reset_clip((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_reset_clip] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_fill
  (ats_cairo_ref cr) {
  cairo_fill((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_fill] */

static inline
ats_void_type
atsctrb_cairo_fill_preserve
  (ats_cairo_ref cr) {
  cairo_fill_preserve((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_fill_preserve] */

static inline
ats_void_type
atsctrb_cairo_fill_extents (
  ats_cairo_ref cr
, ats_ref_type x1, ats_ref_type y1
, ats_ref_type x2, ats_ref_type y2
) {
  cairo_fill_extents(
    (cairo_t*)cr, (double*)x1, (double*)y1, (double*)x2, (double*)y2
  ) ; return ;
} /* end of [atsctrb_cairo_fill_extents] */

static inline
ats_bool_type
atsctrb_cairo_in_fill (
  ats_cairo_ref cr
, ats_double_type x, ats_double_type y
) {
  return cairo_in_fill((cairo_t*)cr, x, y) ;
} /* end of [atsctrb_cairo_in_fill] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_mask (
  ats_cairo_ref cr, ats_cairo_pattern_ref pat
) {
  cairo_mask((cairo_t*)cr, (cairo_pattern_t*)pat) ; return ;
} /* end of [atsctrb_cairo_mask] */

static inline
ats_void_type
atsctrb_cairo_mask_surface (
  ats_cairo_ref cr
, ats_cairo_surface_ref sf
, ats_double_type sf_x, ats_double_type sf_y
) {
  cairo_mask_surface(
    (cairo_t*)cr, (cairo_surface_t*)sf, sf_x, sf_y
  ) ; return ;
} /* end of [atsctrb_cairo_mask_surface] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_paint (
  ats_cairo_ref cr
) {
  cairo_paint((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_paint] */

static inline
ats_void_type
atsctrb_cairo_paint_with_alpha (
  ats_cairo_ref cr, ats_double_type alpha
) {
  cairo_paint_with_alpha((cairo_t*)cr, alpha) ; return ;
} /* end of [atsctrb_cairo_paint_with_alpha] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_stroke (
  ats_cairo_ref cr
) {
  cairo_stroke((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_stroke] */

static inline
ats_void_type
atsctrb_cairo_stroke_preserve (
  ats_cairo_ref cr
) {
  cairo_stroke_preserve((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_stroke_preserve] */

static inline
ats_void_type
atsctrb_cairo_stroke_extents (
  ats_cairo_ref cr
, ats_ref_type x1, ats_ref_type y1
, ats_ref_type x2, ats_ref_type y2
) {
  cairo_stroke_extents(
    (cairo_t*)cr, (double*)x1, (double*)y1, (double*)x2, (double*)y2
  ) ; return ;
} /* end of [atsctrb_cairo_stroke_extents] */

static inline
ats_bool_type
atsctrb_cairo_in_stroke (
  ats_cairo_ref cr
, ats_double_type x, ats_double_type y
) {
  return cairo_in_stroke((cairo_t*)cr, x, y) ;
} /* end of [atsctrb_cairo_in_stroke] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_copy_page
  (ats_cairo_ref cr) {
  cairo_copy_page (cr) ; return ;
} // end of [atsctrb_cairo_copy_page]

static inline
ats_void_type
atsctrb_cairo_show_page
  (ats_cairo_ref cr) {
  cairo_show_page (cr) ; return ;
} // end of [atsctrb_cairo_show_page]

/* ****** ****** */

// drawing paths

/* ****** ****** */

static inline
ats_ref_type
atsctrb_cairo_copy_path
  (ats_cairo_ref cr) {
  return cairo_copy_path((cairo_t*)cr) ; 
} // end of [atsctrb_cairo_copy_path]

static inline
ats_ref_type
atsctrb_cairo_copy_path_flat
  (ats_cairo_ref cr) {
  return cairo_copy_path_flat((cairo_t*)cr) ; 
} // end of [atsctrb_cairo_copy_path_flat]

static inline
ats_void_type
atsctrb_cairo_append_path
  (ats_cairo_ref cr, ats_ref_type path) {
  cairo_append_path((cairo_t*)cr, (cairo_path_t*)path) ;
  return ;
} // end of [atsctrb_cairo_append_path]

static inline
ats_void_type
atsctrb_cairo_path_destroy
  (ats_ref_type path) {
  cairo_path_destroy((cairo_path_t*)path) ; return ;
} // end of [atsctrb_cairo_path_destroy]

/* ****** ****** */

static inline
ats_bool_type
atsctrb_cairo_has_current_point
  (ats_cairo_ref cr) {
  return cairo_has_current_point((cairo_t*)cr) ; 
} // end of [atsctrb_cairo_has_current_point]

static inline
ats_void_type
atsctrb_cairo_get_current_point (
  ats_cairo_ref cr, ats_ref_type x, ats_ref_type y
) {
  cairo_get_current_point((cairo_t*)cr, (double*)x, (double*)y) ;
  return ;
} // end of [atsctrb_cairo_get_current_point]

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_new_path
  (ats_cairo_ref cr) {
  cairo_new_path ((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_new_path] */

static inline
ats_void_type
atsctrb_cairo_new_sub_path
  (ats_cairo_ref cr) {
  cairo_new_sub_path ((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_new_sub_path] */

static inline
ats_void_type
atsctrb_cairo_close_path
  (ats_cairo_ref cr) {
  cairo_close_path ((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_close_path] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_arc (
  ats_cairo_ref cr
, ats_double_type xc, ats_double_type yc
, ats_double_type rad
, ats_double_type angle1, ats_double_type angle2
) {
  cairo_arc ((cairo_t*)cr, xc, yc, rad, angle1, angle2) ;
  return ;
} /* end of [atsctrb_cairo_arc] */

static inline
ats_void_type
atsctrb_cairo_arc_negative (
  ats_cairo_ref cr
, ats_double_type xc, ats_double_type yc
, ats_double_type rad
, ats_double_type angle1, ats_double_type angle2
) {
  cairo_arc_negative ((cairo_t*)cr, xc, yc, rad, angle1, angle2) ;
  return ;
} /* end of [atsctrb_cairo_arc_negative] */

static inline
ats_void_type
atsctrb_cairo_curve_to (
  ats_cairo_ref cr
, ats_double_type x1, ats_double_type y1
, ats_double_type x2, ats_double_type y2
, ats_double_type x3, ats_double_type y3
) {
  cairo_curve_to ((cairo_t*)cr, x1, y1, x2, y2, x3, y3) ;
  return ;
} /* end of [atsctrb_cairo_curve_to] */

static inline
ats_void_type
atsctrb_cairo_line_to (
  ats_cairo_ref cr
, ats_double_type x, ats_double_type y
) {
  cairo_line_to ((cairo_t*)cr, x, y) ; return ;
} /* end of [atsctrb_cairo_line_to] */

static inline
ats_void_type
atsctrb_cairo_move_to (
  ats_cairo_ref cr
, ats_double_type x, ats_double_type y
) {
  cairo_move_to ((cairo_t*)cr, x, y) ; return ;
} /* end of [atsctrb_cairo_move_to] */

static inline
ats_void_type
atsctrb_cairo_rectangle (
  ats_cairo_ref cr
, ats_double_type x, ats_double_type y
, ats_double_type w, ats_double_type h
) {
  cairo_rectangle ((cairo_t*)cr, x, y, w, h) ; return ;
} /* end of [atsctrb_cairo_rectangle] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_rel_curve_to (
  ats_cairo_ref cr
, ats_double_type x1, ats_double_type y1
, ats_double_type x2, ats_double_type y2
, ats_double_type x3, ats_double_type y3
) {
  cairo_rel_curve_to ((cairo_t*)cr, x1, y1, x2, y2, x3, y3) ;
  return ;
} /* end of [atsctrb_cairo_rel_curve_to] */

static inline
ats_void_type
atsctrb_cairo_rel_line_to (
  ats_cairo_ref cr
, ats_double_type x, ats_double_type y
) {
  cairo_rel_line_to ((cairo_t*)cr, x, y) ; return ;
} /* end of [atsctrb_cairo_rel_line_to] */

static inline
ats_void_type
atsctrb_cairo_rel_move_to (
  ats_cairo_ref cr
, ats_double_type x, ats_double_type y
) {
  cairo_rel_move_to ((cairo_t*)cr, x, y) ; return ;
} /* end of [atsctrb_cairo_rel_move_to] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_path_extents (
  ats_cairo_ref cr
, ats_ref_type x1, ats_ref_type y1
, ats_ref_type x2, ats_ref_type y2
) {
  cairo_path_extents(
    (cairo_t*)cr, (double*)x1, (double*)y1, (double*)x2, (double*)y2
  ) ; return ;
} /* end of [atsctrb_cairo_path_extents] */

/* ****** ****** */

// drawing texts

static inline
ats_void_type
atsctrb_cairo_select_font_face (
  ats_cairo_ref cr, ats_ptr_type name
, ats_cairo_font_slant_type slnt
, ats_cairo_font_weight_type wght
) {
  cairo_select_font_face((cairo_t*)cr, name, slnt, wght) ; return ;
} /* end of [atsctrb_cairo_select_font_face] */

static inline
ats_void_type
atsctrb_cairo_set_font_size (
  ats_cairo_ref cr, ats_double_type size
) {
  cairo_set_font_size((cairo_t*)cr, size) ; return ;
} /* end of [atsctrb cairo_set_font_size] */

/* ****** ****** */

static inline
ats_cairo_font_face_ref
atsctrb_cairo_get_font_face (
  ats_cairo_ref cr
) {
  return cairo_get_font_face((cairo_t*)cr) ;
} /* end of [atsctrb cairo_get_font_face] */

static inline
ats_void_type
atsctrb_cairo_set_font_face (
  ats_cairo_ref cr, ats_cairo_font_face_ref face
) {
  cairo_set_font_face((cairo_t*)cr, (cairo_font_face_t*)face) ;
  return ;
} /* end of [atsctrb cairo_set_font_face] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_font_extents (
  ats_cairo_ref cr, ats_ref_type extents
) {
  cairo_font_extents (
    (cairo_t*)cr, (cairo_font_extents_t*)extents
  ) ; return ;
} // end of [atsctrb_cairo_font_extents]

static inline
ats_void_type
atsctrb_cairo_text_extents (
  ats_cairo_ref cr, ats_ptr_type utf8, ats_ref_type extents
) {
  cairo_text_extents (
    (cairo_t*)cr, (char*)utf8, (cairo_text_extents_t*)extents
  ) ; return ;
} // end of [atsctrb_cairo_text_extents]

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_show_text (
  ats_cairo_ref cr, ats_ptr_type utf8
) {
  cairo_show_text((cairo_t*)cr, (char*)utf8) ; return ;
} /* end of [atsctrb cairo_show_text] */

/* ****** ****** */

// transformations for drawing

static inline
ats_void_type
atsctrb_cairo_translate (
  ats_cairo_ref cr
, ats_double_type sx, ats_double_type sy
) {
  cairo_translate((cairo_t*)cr, sx, sy) ; return ;
}

static inline
ats_void_type
atsctrb_cairo_scale (
  ats_cairo_ref cr
, ats_double_type sx, ats_double_type sy
) {
  cairo_scale((cairo_t*)cr, sx, sy) ; return ;
}

static inline
ats_void_type
atsctrb_cairo_rotate (
  ats_cairo_ref cr
, ats_double_type angle
) {
  cairo_rotate((cairo_t*)cr, angle) ; return ;
} // end of [atsctrb_cairo_rotate]

static inline
ats_void_type
atsctrb_cairo_transform (
  ats_cairo_ref cr, ats_ref_type mat
) {
  cairo_transform ((cairo_t*)cr, (cairo_matrix_t*)mat) ;
  return ;
} // end of [atsctrb_cairo_transform]

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_get_matrix (
  ats_cairo_ref cr, ats_ref_type mat
) {
  cairo_get_matrix ((cairo_t*)cr, (cairo_matrix_t*)mat) ;
  return ;
} // end of [atsctrb_cairo_get_matrix]

static inline
ats_void_type
atsctrb_cairo_set_matrix (
  ats_cairo_ref cr, ats_ref_type mat
) {
  cairo_set_matrix ((cairo_t*)cr, (cairo_matrix_t*)mat) ;
  return ;
} // end of [atsctrb_cairo_set_matrix]

static inline
ats_void_type
atsctrb_cairo_identity_matrix
  (ats_cairo_ref cr) {
  cairo_identity_matrix ((cairo_t*)cr) ; return ;
} // end of [atsctrb_cairo_identity_matrix]

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_user_to_device (
  ats_cairo_ref cr
, ats_ref_type x, ats_ref_type y
) {
  cairo_user_to_device((cairo_t*)cr, (double*)x, (double*)y) ;
  return ;
} // end of [atsctrb_cairo_user_to_device]

static inline
ats_void_type
atsctrb_cairo_user_to_device_distance (
  ats_cairo_ref cr, ats_ref_type dx, ats_ref_type dy
) {
  cairo_user_to_device_distance((cairo_t*)cr, (double*)dx, (double*)dy) ;
  return ;
} // end of [atsctrb_cairo_user_to_device_distance]

static inline
ats_void_type
atsctrb_cairo_device_to_user (
  ats_cairo_ref cr
, ats_ref_type x, ats_ref_type y
) {
  cairo_device_to_user((cairo_t*)cr, (double*)x, (double*)y) ;
  return ;
} // end of [atsctrb_cairo_device_to_user]

static inline
ats_void_type
atsctrb_cairo_device_to_user_distance (
  ats_cairo_ref cr, ats_ref_type dx, ats_ref_type dy
) {
  cairo_device_to_user_distance((cairo_t*)cr, (double*)dx, (double*)dy) ;
  return ;
} // end of [atsctrb_cairo_device_to_user_distance]

/* ****** ****** */

//
// surfaces for drawing
//

static inline
ats_void_type
atsctrb_cairo_surface_destroy
  (ats_cairo_surface_ref sf) {
  cairo_surface_destroy((cairo_surface_t*)sf) ; return ;
}

/* ****** ****** */

// image surface

static inline
ats_cairo_surface_ref
atsctrb_cairo_image_surface_create (
  ats_cairo_format_type fmt
, ats_int_type w, ats_int_type h
) {
  return cairo_image_surface_create(fmt, w, h) ;
} /* end of [atsctrb_cairo_image_surface_create] */

static inline
ats_cairo_surface_ref
atsctrb_cairo_image_surface_create_from_png
  (ats_ptr_type filename) {
  return cairo_image_surface_create_from_png((char*)filename) ;
} // end of [atsctrb_cairo_image_surface_create_from_png]

static inline
ats_cairo_surface_ref
atsctrb_cairo_image_surface_create_from_png_stream
  (ats_fun_ptr_type fread, ats_ptr_type env) {
  return cairo_image_surface_create_from_png_stream(
    (cairo_read_func_t)fread, env
  ) ; // end of [return]
} // end of [atsctrb_cairo_image_surface_create_from_png_stream]

static inline
ats_double_type
atsctrb_cairo_image_surface_get_width
  (ats_ptr_type image) {
  return cairo_image_surface_get_width (image) ;
} /* end of [atsctrb_cairo_image_surface_get_width] */

static inline
ats_double_type
atsctrb_cairo_image_surface_get_height
  (ats_ptr_type image) {
  return cairo_image_surface_get_height (image) ;
} /* end of [atsctrb_cairo_image_surface_get_height] */

static inline
ats_double_type
atsctrb_cairo_image_surface_get_stride
  (ats_ptr_type image) {
  return cairo_image_surface_get_stride (image) ;
} /* end of [atsctrb_cairo_image_surface_get_stride] */

/* ****** ****** */

static inline
ats_cairo_status_type
atsctrb_cairo_surface_write_to_png
  (ats_cairo_surface_ref sf, ats_ptr_type filename) {
  return cairo_surface_write_to_png ((cairo_surface_t*)sf, (char*)filename) ;
} /* end of [atsctrb_cairo_surface_write_to_png] */

static inline
ats_cairo_status_type
atsctrb_cairo_surface_write_to_png_stream(
  ats_cairo_surface_ref sf
, ats_fun_ptr_type fwrite, ats_ptr_type env
) {
  return cairo_surface_write_to_png_stream (
    (cairo_surface_t*)sf, (cairo_write_func_t)fwrite, env
  ) ; // end of [return]
} /* end of [atsctrb_cairo_surface_write_to_png_stream] */

/* ****** ****** */

// PDF surface

#if (CAIRO_HAS_PDF_SURFACE)

static inline
ats_cairo_surface_ref
atsctrb_cairo_pdf_surface_create (
  ats_ptr_type filename
, ats_double_type w_pts, ats_double_type h_pts
) {
  return cairo_pdf_surface_create((char*)filename, w_pts, h_pts) ;
} /* end of [atsctrb_cairo_pdf_surface_create] */

static inline
ats_cairo_surface_ref
atsctrb_cairo_pdf_surface_create_null (
  ats_double_type w_pts, ats_double_type h_pts
) {
  return cairo_pdf_surface_create((char*)0, w_pts, h_pts) ;
} /* end of [atsctrb_cairo_pdf_surface_create_null] */

static inline
ats_cairo_surface_ref
atsctrb_cairo_pdf_surface_create_for_stream (
  ats_fun_ptr_type fwrite, ats_ptr_type env
, ats_double_type w_pts, ats_double_type h_pts
) {
  return cairo_pdf_surface_create_for_stream(
    (cairo_write_func_t)fwrite, (ats_ptr_type)env, w_pts, h_pts
  ) ; // end of [return]
} // end of [atsctrb_cairo_pdf_surface_create_for_stream]

static inline
ats_void_type
atsctrb_cairo_pdf_surface_set_size (
  ats_cairo_surface_ref sf
, ats_double_type w_pts, ats_double_type h_pts
) {
  cairo_pdf_surface_set_size((cairo_surface_t*)sf, w_pts, h_pts) ;
  return ;
} /* end of [atsctrb_cairo_pdf_surface_set_size] */

#endif // end of [CAIRO_HAS_PDF_SURFACE]

/* ****** ****** */

// PS surface

#if (CAIRO_HAS_PS_SURFACE)

static inline
ats_cairo_surface_ref
atsctrb_cairo_ps_surface_create (
  ats_ptr_type filename
, ats_double_type w_pts, ats_double_type h_pts
) {
  return cairo_ps_surface_create((char*)filename, w_pts, h_pts) ;
} /* end of [atsctrb_cairo_ps_surface_create] */

static inline
ats_cairo_surface_ref
atsctrb_cairo_ps_surface_create_null (
  ats_double_type w_pts, ats_double_type h_pts
) {
  return cairo_ps_surface_create((char*)0, w_pts, h_pts) ;
} /* end of [atsctrb_cairo_ps_surface_create_null] */

static inline
ats_cairo_surface_ref
atsctrb_cairo_ps_surface_create_for_stream (
  ats_fun_ptr_type fwrite, ats_ptr_type env
, ats_double_type w_pts, ats_double_type h_pts
) {
  return cairo_ps_surface_create_for_stream(
    (cairo_write_func_t)fwrite, (ats_ptr_type)env, w_pts, h_pts
  ) ; // end of [return]
} // end of [atsctrb_cairo_ps_surface_create_for_stream]

/*
typedef cairo_ps_level_t ats_cairo_ps_level_type ;

ats_ref_type
atsctrb_cairo_ps_get_levels
  (ats_ref_type num_levels) {
  cairo_ps_level_t **p_levels ;
  cairo_ps_get_levels (p_levels, (int*)num_levels) ;
  return (ats_ref_type)(*p_levels) ;
} // end of [cairo_ps_get_levels]
*/

static inline
ats_void_type
atsctrb_cairo_ps_surface_set_size (
  ats_cairo_surface_ref sf
, ats_double_type w_pts, ats_double_type h_pts
) {
  cairo_ps_surface_set_size((cairo_surface_t*)sf, w_pts, h_pts) ;
  return ;
} /* end of [atsctrb_cairo_ps_surface_set_size] */

static inline
ats_void_type
atsctrb_cairo_ps_surface_dsc_begin_setup
  (ats_cairo_surface_ref sf) {
  cairo_ps_surface_dsc_begin_setup (sf) ; return ;
} // end of [atsctrb_cairo_ps_surface_dsc_begin_setup]

static inline
ats_void_type
atsctrb_cairo_ps_surface_dsc_begin_page_setup
  (ats_cairo_surface_ref sf) {
  cairo_ps_surface_dsc_begin_page_setup (sf) ; return ;
} // end of [atsctrb_cairo_ps_surface_dsc_begin_page_setup]

static inline
ats_void_type
atsctrb_cairo_ps_surface_dsc_comment
  (ats_cairo_surface_ref sf, ats_ptr_type comment) {
  cairo_ps_surface_dsc_comment (sf, (char*)comment) ;
  return ;
} // end of [atsctrb_cairo_ps_surface_dsc_comment]

#endif // end of [CAIRO_HAS_PS_SURFACE]

/* ****** ****** */

//
// utilities for drawing
//

/* ****** ****** */

// generic matrix operations

static inline
ats_void_type
atsctrb_cairo_matrix_init (
  ats_ref_type matrix
, ats_double_type xx, ats_double_type yx
, ats_double_type xy, ats_double_type yy
, ats_double_type x0, ats_double_type y0
) {
  cairo_matrix_init((cairo_matrix_t*)matrix, xx, yx, xy, yy, x0, y0) ;
  return ;
} /* end of [atsctrb_cairo_matrix_init] */

static inline
ats_void_type
atsctrb_cairo_matrix_init_identity (
  ats_ref_type matrix
) {
  cairo_matrix_init_identity((cairo_matrix_t*)matrix) ; return ;
} /* end of [atsctrb_cairo_matrix_init_identity] */

static inline
ats_void_type
atsctrb_cairo_matrix_init_translate (
  ats_ref_type matrix
, ats_double_type tx, ats_double_type ty
) {
  cairo_matrix_init_translate((cairo_matrix_t*)matrix, tx, ty) ;
  return ;
} /* end of [atsctrb_cairo_matrix_init_translate] */

static inline
ats_void_type
atsctrb_cairo_matrix_init_scale (
  ats_ref_type matrix
, ats_double_type sx, ats_double_type sy
) {
  cairo_matrix_init_scale((cairo_matrix_t*)matrix, sx, sy) ;
  return ;
} /* end of [atsctrb_cairo_matrix_init_scale] */

static inline
ats_void_type
atsctrb_cairo_matrix_init_rotate (
  ats_ref_type matrix
, ats_double_type angle
) {
  cairo_matrix_init_rotate((cairo_matrix_t*)matrix, angle) ;
  return ;
} /* end of [atsctrb_cairo_matrix_init_rotate] */

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_matrix_translate (
  ats_ref_type matrix
, ats_double_type tx, ats_double_type ty
) {
  cairo_matrix_translate((cairo_matrix_t*)matrix, tx, ty) ;
  return ;
} /* end of [atsctrb_cairo_matrix_translate] */

static inline
ats_void_type
atsctrb_cairo_matrix_scale (
  ats_ref_type matrix
, ats_double_type sx, ats_double_type sy
) {
  cairo_matrix_scale((cairo_matrix_t*)matrix, sx, sy) ;
  return ;
} /* end of [atsctrb_cairo_matrix_scale] */

static inline
ats_void_type
atsctrb_cairo_matrix_rotate (
  ats_ref_type matrix
, ats_double_type angle
) {
  cairo_matrix_rotate((cairo_matrix_t*)matrix, angle) ;
  return ;
} /* end of [atsctrb_cairo_matrix_rotate] */

/* ****** ****** */

static inline
ats_cairo_status_type
atsctrb_cairo_matrix_invert
  (ats_ref_type matrix) {
  return cairo_matrix_invert(matrix) ;
} // end of [atsctrb_cairo_matrix_invert]

static inline
ats_void_type
atsctrb_cairo_matrix_multiply (
  ats_ref_type result
, ats_ref_type a, ats_ref_type b
) {
  cairo_matrix_multiply(
    (cairo_matrix_t*)result
  , (cairo_matrix_t*)a, (cairo_matrix_t*)b
  ) ; return ;
} // end of [atsctrb_cairo_matrix_multiply]

static inline
ats_void_type
atsctrb_cairo_matrix_transform_distance (
  ats_ref_type matrix
, ats_ref_type dx, ats_ref_type dy
) {
  cairo_matrix_transform_distance(
    (cairo_matrix_t*)matrix, (double*)dx, (double*)dy
  ) ; return ;
} // end of [atsctrb_cairo_matrix_transform_distance]

static inline
ats_void_type
atsctrb_cairo_matrix_transform_point (
  ats_ref_type matrix
, ats_ref_type x, ats_ref_type y
) {
  cairo_matrix_transform_point(
    (cairo_matrix_t*)matrix, (double*)x, (double*)y
  ) ; return ;
} // end of [atsctrb_cairo_matrix_transform_point]

/* ****** ****** */

static inline
ats_uint_type
atsctrb_cairo_get_reference_count
  (ats_cairo_ref cr) {
  return cairo_get_reference_count((cairo_t*)cr) ;
} // end of [atsctrb_cairo_get_reference_count]

/* ****** ****** */

static inline
ats_ptr_type // string
atsctrb_cairo_status_to_string
  (ats_cairo_status_type status) {
  return (ats_ptr_type)cairo_status_to_string(status) ;
} // end of [atsctrb_cairo_status_to_string]

static inline
ats_void_type
atsctrb_cairo_debug_reset_static_data () {
  cairo_debug_reset_static_data() ; return ;
} // end of [atsctrb_cairo_debug_reset_static_data]

/* ****** ****** */

#endif // end of [ATSCTRB_CAIRO_CAIRO_CATS]

/* end of [cairo.cats] */
