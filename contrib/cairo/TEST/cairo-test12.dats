(*
**
** A simple CAIRO example: filling rules
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: March, 2010
**
*)

(*
** how to compile:
   atscc -o test12 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test12.dats

** how ot test:
   ./test12
   'gthumb' can be used to view the generated image file 'cairo-test12.png'
*)

(* ****** ****** *)

staload M = "libc/SATS/math.sats"
macdef PI = $M.M_PI

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

implement main () = () where {
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, 256, 256)
  val cr = cairo_create (surface)
//
  val pat = cairo_pattern_create_linear (0.0, 0.0, 0.0, 256.0)
  val () = cairo_pattern_add_color_stop_rgba (pat, 1.0, 0.0, 0.0, 0.0, 1.0)
  val () = cairo_pattern_add_color_stop_rgba (pat, 0.0, 1.0, 1.0, 1.0, 1.0)
  val () = cairo_set_source (cr, pat)
  val () = cairo_rectangle (cr, 0.0, 0.0, 256.0, 256.0)
  val () = cairo_fill (cr)
  val () = cairo_pattern_destroy (pat)
//
  val pat = cairo_pattern_create_radial (115.2, 102.4, 25.6, 102.4, 102.4, 128.0)
  val () = cairo_pattern_add_color_stop_rgba (pat, 1.0, 0.0, 0.0, 0.0, 1.0)
  val () = cairo_pattern_add_color_stop_rgba (pat, 0.0, 1.0, 1.0, 1.0, 1.0)
  val () = cairo_set_source (cr, pat)
  val () = cairo_arc (cr, 128.0, 128.0, 76.8, 0.0, 2*PI)
  val () = cairo_fill (cr)
  val () = cairo_pattern_destroy (pat)
//
  val status = cairo_surface_write_to_png (surface, "cairo-test12.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test12.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test12.dats] *)
