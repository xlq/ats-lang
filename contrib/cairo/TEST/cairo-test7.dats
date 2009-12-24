(*
**
** A simple CAIRO example: a clock @ home
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2009
**
*)

(*
** how to compile:
   atscc -o test7 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test7.dats

** how ot test:
   ./test7
   'gthumb' can be used to view the generated image file 'cairo-test7.png'
*)

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

stadef dbl = double
stadef cr = cairo_ref

(* ****** ****** *)

fn draw_clock
  (cr: !cr, h: natLt 24, m: natLt 60): void = let
//
  val h = (if h >= 12 then h - 12 else h): natLt 12
  val m_ang = m * (1.0 / 30) * M_PI - M_PI/2
  val h_ang = h * (1.0 / 6) * M_PI + m * (1.0 / 360) * M_PI - M_PI/2
//
  val rad = 100.0
  val () = cairo_arc
    (cr, 0.0, 0.0, rad, 0.0, 2 * M_PI)
  val () = cairo_set_source_rgb (cr, 1.0, 1.0, 1.0)
  val () = cairo_fill (cr)
  val () = cairo_arc
    (cr, 0.0, 0.0, rad, 0.0, 2 * M_PI)
  val () = cairo_set_source_rgb (cr, 0.0, 1.0, 0.0)
  val () = cairo_set_line_width (cr, 10.0)
  val () = cairo_stroke (cr)
//
  val rad1 = 0.80 * rad
  val () = cairo_arc (cr, ~rad1, ~rad1, rad1, 0.0,  M_PI/2)
  val () = cairo_arc (cr, ~rad1,  rad1, rad1, ~M_PI/2, 0.0)
  val () = cairo_arc (cr,  rad1,  rad1, rad1, ~M_PI, ~M_PI/2)
  val () = cairo_arc (cr,  rad1, ~rad1, rad1, M_PI/2, M_PI)
  val () = cairo_fill (cr)
//
  val h_l = 0.60 * rad
  val () = cairo_move_to (cr, 0.0, 0.0)
  val () = cairo_rel_line_to (cr, h_l * cos (h_ang), h_l * sin (h_ang))
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = cairo_set_line_width (cr, 6.5)
  val () = cairo_stroke (cr)
//
  val m_l = 0.85 * rad
  val () = cairo_move_to (cr, 0.0, 0.0)
  val () = cairo_rel_line_to (cr, m_l * cos (m_ang), m_l * sin (m_ang))
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = cairo_set_line_width (cr, 5.0)
  val () = cairo_stroke (cr)
//

  val () = cairo_new_sub_path (cr)
  val () = cairo_arc (cr, 0.0, 0.0, 8.0, 0.0, 2 * M_PI)  
  val () = cairo_fill (cr)
in
  // nothing
end // end of [draw_clock]

(* ****** ****** *)

implement main () = () where {
//
  val hr = 10 and min = 19
//
  val wd = 300 and ht = 300
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, wd, ht)
  val cr = cairo_create (surface)
//
  val wd = double_of wd and ht = double_of ht
  val xc = wd / 2 and yc = ht / 2
  val rad = 0.75 * min_double_double (xc, yc)
//
  val () = cairo_translate (cr, xc, yc)
  val () = draw_clock (cr, hr, min)
//
  val status = cairo_surface_write_to_png (surface, "cairo-test7.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test7.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test7.dats] *)
