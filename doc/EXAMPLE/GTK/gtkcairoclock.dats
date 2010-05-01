(*
**
** A simple GTK/CAIRO example: a clock @ home
** The part of clock drawing is largely taken from
** a cairo example I did in December 2009
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "libc/SATS/math.sats"
macdef PI = M_PI
macdef PI2 = PI/2

staload "libc/SATS/time.sats"

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

stadef dbl = double
stadef cr (l:addr) = cairo_ref l

(* ****** ****** *)

fn draw_hand {l:agz}
  (cr: !cr l, bot: dbl, top:dbl, len: dbl): void = let
  val () = cairo_move_to (cr, 0.0, bot/2)
  val () = cairo_line_to (cr, len, top/2)
  val () = cairo_line_to (cr, len, ~top/2)
  val () = cairo_line_to (cr, 0.0, ~bot/2)
  val () = cairo_close_path (cr)
in
  cairo_fill (cr)
end // end of [draw_hand]

(* ****** ****** *)

val theLastSec = ref_make_elt<int> (~1)

fn draw_clock {l:agz} (
    cr: !cr l
  , h: natLt 24, m: natLt 60, s: natLt 60 // hour and minute
  ) : void = let
//
  val dim = 100.0 // please scale it!
  val rad = 0.375 * dim
//
  val h = (if h >= 12 then h - 12 else h): natLt 12
  val s_ang = s * (PI / 30) - PI2
  // val m_ang = m * (PI / 30) + s * (PI / 1800) - PI2
  val m_ang = m * (PI / 30) - PI2
  val h_ang = h * (PI / 6) + m * (PI / 360) - PI2
//
  val () = cairo_arc
    (cr, 0.0, 0.0, rad, 0.0, 2 * PI)
  val () = cairo_set_source_rgb (cr, 1.0, 1.0, 1.0)
(*
  val () = cairo_set_source_rgb (cr, 1.0, 0.50, 0.50)
*)
  val () = cairo_fill (cr)
  val () = cairo_arc
    (cr, 0.0, 0.0, rad, 0.0, 2 * PI)
  val () = cairo_set_source_rgb (cr, 0.0, 1.0, 0.0)
(*
  val () = cairo_set_source_rgb (cr, 1.0, 0.0, 1.0)
*)
  val () = cairo_set_line_width (cr, 4.0)
  val () = cairo_stroke (cr)
//
  val rad1 = 0.90 * rad
  val () = cairo_arc (cr, ~rad1, ~rad1, rad1,  0.0, PI2)
  val () = cairo_arc (cr, ~rad1,  rad1, rad1, ~PI2,  0.)
  val () = cairo_arc (cr,  rad1,  rad1, rad1, ~PI, ~PI2)
  val () = cairo_arc (cr,  rad1, ~rad1, rad1,  PI2,  PI)
  val () = cairo_fill (cr)
//
  val h_l = 0.60 * rad
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = cairo_rotate (cr, h_ang)
  val () = draw_hand (cr, 3.0, 1.5, h_l)
  val () = cairo_restore (pf | cr)
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = cairo_rotate (cr, h_ang+PI)
  val () = draw_hand (cr, 3.0, 1.5, h_l/4)
  val () = cairo_restore (pf | cr)
//
  val m_l = 0.85 * rad
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = cairo_rotate (cr, m_ang)
  val () = draw_hand (cr, 2.0, 1.0, m_l)
  val () = cairo_restore (pf | cr)
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = cairo_rotate (cr, m_ang+PI)
  val () = draw_hand (cr, 2.0, 1.0, h_l/4)
  val () = cairo_restore (pf | cr)
//
  val s_l = 0.85 * rad
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgb (cr, 1.0, 0.0, 0.0)
  val () = cairo_rotate (cr, s_ang)
  val () = draw_hand (cr, 1.0, 0.5, m_l)
  val () = cairo_restore (pf | cr)
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgb (cr, 1.0, 0.0, 0.0)
  val () = cairo_rotate (cr, s_ang+PI)
  val () = draw_hand (cr, 1.0, 0.5, h_l/4)
  val () = cairo_restore (pf | cr)
//
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = cairo_new_sub_path (cr)
  val () = cairo_arc (cr, 0.0, 0.0, 2.5, 0.0, 2 * PI)  
  val () = cairo_fill (cr)
  val () = cairo_restore (pf | cr)
in
  // nothing
end // end of [draw_clock]

(* ****** ****** *)

extern fun draw_main {l:agz}
  (cr: !cairo_ref l, width: int, height: int)
  : void = "draw_main"
implement draw_main
  (cr, width, height) = () where {
  val w = (double_of)width
  val h = (double_of)height
  val mn = min (w, h)
  val xc = w / 2 and yc = h / 2
  val (pf0 | ()) = cairo_save (cr)
  val () = cairo_translate (cr, xc, yc)
  val alpha = mn / 100
  val () = cairo_scale (cr, alpha, alpha)
//
  var t: time_t // unintialized
  val _(*ignored*) = time_get_and_set (t)
  var tm: tm_struct // unintialized
  val () = localtime_r (t, tm)
  val hr = tm.tm_hour and mt = tm.tm_min and sd = tm.tm_sec
  val hr = int1_of_int (hr)
  val () = assert (0 <= hr && hr < 24)
  val mt = int1_of_int (mt)
  val () = assert (0 <= mt && mt < 60)
  val sd = int1_of_int (sd)
  val () = assert (0 <= sd && sd < 60)
  val () = draw_clock (cr, hr, mt, sd)
//
  val () = cairo_restore (pf0 | cr)
} // end of [val]

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

%{^
GtkWidget *the_drawingarea = NULL;
ats_ptr_type
the_drawingarea_get () {
  g_object_ref (G_OBJECT(the_drawingarea)); return the_drawingarea ;
}
ats_void_type
the_drawingarea_set (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (the_drawingarea) g_object_unref (G_OBJECT(the_drawingarea));
  the_drawingarea = x ;
  return ;
} // end of [the_drawingarea_set]
%} // end of [%{^] 
extern fun the_drawingarea_get (): GtkDrawingArea_ptr1 = "the_drawingarea_get"
extern fun the_drawingarea_set (x: !GtkDrawingArea_ptr1): void = "the_drawingarea_set"

(* ****** ****** *)

extern fun gdk_cairo_create
  {c:cls | c <= GdkDrawable} {l:agz} (widget: !gobjptr (c, l)): cairo_ref1
  = "#gdk_cairo_create"
// end of [gdk_cairo_create]

fun draw_drawingarea
  {c:cls | c <= GtkDrawingArea} {l:agz}
  (darea: !gobjptr (c, l)): void = let
  val (fpf_win | win) = gtk_widget_takeout_window (darea)
in
  if g_object_isnot_null (win) then let
    val cr = gdk_cairo_create (win)
    prval () = fpf_win (win)
    val (pf, fpf | p) = gtk_widget_takeout_allocation (darea)
    val () = draw_main (cr, (int_of)p->width, (int_of)p->height)
    prval () = minus_addback (fpf, pf | darea)
    val () = cairo_destroy (cr)
  in
    // nothing
  end else let
    prval () = fpf_win (win)
  in
    // nothing
  end (* end of [if] *)
end // end of [draw_drawingarea]

(* ****** ****** *)

fun fexpose (): gboolean = let
  val darea = the_drawingarea_get ()
  val _ = draw_drawingarea (darea)
  val () = g_object_unref (darea)
in
  GFALSE
end // end of [fexpose]

(* ****** ****** *)

fun sec_changed
  (): bool = let
  var t: time_t // unintialized
  val _(*ignored*) = time_get_and_set (t)
  var tm: tm_struct // unintialized
  val () = localtime_r (t, tm)
  val sd = tm.tm_sec
  val sd_old = !theLastSec
in
  sd <> sd_old
end // end of [sec_changed]

fun ftimeout
  (_: gpointer): gboolean = let
  val [l:addr] darea = the_drawingarea_get ()
  val (fpf_win | win) = gtk_widget_takeout_window (darea)
in
  if g_object_isnot_null (win) then let
    prval () = fpf_win (win)
    val (pf, fpf | p) = gtk_widget_takeout_allocation (darea)
    val () = if sec_changed () then
      gtk_widget_queue_draw_area (darea, (gint)0, (gint)0, p->width, p->height)
    // end of [val]
    prval () = minus_addback (fpf, pf | darea)
    val () = g_object_unref (darea)
  in
    GTRUE
  end else let
    prval () = fpf_win (win)  
    val () = g_object_unref (darea)
  in
    GFALSE
  end // end of [if]
end // end of [ftimeout]

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_window_set_default_size (window, (gint)400, (gint)400)
  val () = gtk_window_set_title (window, "gtkcairoclock")
  val darea = gtk_drawing_area_new ()
  val () = the_drawingarea_set (darea)
  val () = gtk_container_add (window, darea)
  val _sid = g_signal_connect
    (darea, (gsignal)"expose-event", G_CALLBACK (fexpose), (gpointer)null)
  val () = g_object_unref (darea)
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect0
    (window_, (gsignal)"delete-event", G_CALLBACK (gtk_main_quit), (gpointer)null)
  val _sid = g_signal_connect1
    (window, (gsignal)"destroy-event", G_CALLBACK (gtk_widget_destroy), (gpointer)null)
//
  val _rid = gtk_timeout_add ((guint32)100U, ftimeout, (gpointer)null)
  val () = gtk_widget_show_all (window)
  prval () = fpf_window (window)
  val () = gtk_main ()
} // end of [val]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$
ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  gtk_init ((int*)&argc, (char***)&argv) ;
  main1 () ;
  return ;
} // end of [mainats]
%} // end of [%{$]

(* ****** ****** *)

(* end of [gtkcairolock.dats] *)