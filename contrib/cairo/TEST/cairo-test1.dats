(*
**
** A simple CAIRO example
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2009
**
*)

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

implement main () = () where {
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, 250, 80)
  val cr = cairo_create (surface)
//
(*
  val () = cairo_select_font_face
    (cr, "serif", CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_NORMAL)
*)
  val () = cairo_select_font_face
    (cr, "Sans", CAIRO_FONT_SLANT_ITALIC, CAIRO_FONT_WEIGHT_BOLD)
  val () = cairo_set_font_size (cr, 32.0)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 1.0)
  val () = cairo_move_to (cr, 10.0, 50.0)
  val () = cairo_show_text (cr, "Hello, world!")
//
  val status = cairo_surface_write_to_png (surface, "hello.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [hello.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test1.dats] *)
