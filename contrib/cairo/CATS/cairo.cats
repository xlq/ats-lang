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

/* ****** ****** */

static inline
ats_void_type
atsctrb_cairo_fill (
  ats_cairo_ref cr
) {
  cairo_fill((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_fill] */

static inline
ats_void_type
atsctrb_cairo_fill_preserve (
  ats_cairo_ref cr
) {
  cairo_fill_preserve((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_fill_preserve] */

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
atsctrb_cairo_paint (
  ats_cairo_ref cr
) {
  cairo_paint((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_paint] */

static inline
ats_void_type
atsctrb_cairo_stroke (
  ats_cairo_ref cr
) {
  cairo_stroke((cairo_t*)cr) ; return ;
} /* end of [atsctrb_cairo_stroke] */

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
}

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
  return cairo_image_surface_create_from_png ((char*)filename) ;
} /* end of [atsctrb_cairo_image_surface_create_from_png] */

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
