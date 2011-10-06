(*
**
** A simple GTK/CAIRO example:
** Illustrating a famous theorm of Pascal's
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Summer, 2010
**
*)

(* ****** ****** *)

staload _ = "prelude/DATS/list_vt.dats"
staload _ = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "libc/SATS/math.sats"

macdef PI = M_PI
macdef _2PI = 2*PI

staload "libc/SATS/random.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"

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
extern fun the_drawingarea_get (): GtkDrawingArea_ref1 = "the_drawingarea_get"
extern fun the_drawingarea_set (x: !GtkDrawingArea_ref1): void = "the_drawingarea_set"

(* ****** ****** *)

fun fnext () = () where {
  val ts = genRandDoubles (6)
  val ts = sort (ts)
  val ts = list0_of_list_vt (ts) // no-op
  val () = !theVertexLst := ts
  val darea = the_drawingarea_get ()
  val (pf, fpf | p) = gtk_widget_getref_allocation (darea)
  val () = gtk_widget_queue_draw_area (darea, (gint)0, (gint)0, p->width, p->height)
  prval () = minus_addback (fpf, pf | darea)
  val () = g_object_unref (darea)
} // end of [fnext]

fun draw_main {l:agz} (
    cr: !cairo_ref l, W: int, H: int
  ) : void = () where {
  val W = (double_of)W
  and H = (double_of)H
  val () = draw_pascal_theorem (cr, W, H)
} // end of [draw_main]

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

fun fexpose
  {c:cls | c <= GtkDrawingArea} {l:agz}
  (darea: !gobjref (c, l), event: &GdkEvent): gboolean = let
  prval () = clstrans {c,GtkDrawingArea,GtkWidget} ()
  val (fpf_win | win) = gtk_widget_get_window (darea)
  val () = assert_errmsg (g_object_isnot_null (win), #LOCATION)
  val cr = gdk_cairo_create (win)
  prval () = minus_addback (fpf_win, win | darea)
  val (pf, fpf | p) = gtk_widget_getref_allocation (darea)
  val () = draw_main (cr, (int_of)p->width, (int_of)p->height)
  prval () = minus_addback (fpf, pf | darea)
  val () = cairo_destroy (cr)
in
  GFALSE // HX: what does this mean?
end // end of [fexpose]

(* ****** ****** *)

macdef gs = gstring_of_string

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
//
  val () = srand48_with_time ()
//
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () =
    gtk_window_set_default_size (window, (gint)400, (gint)400)
  // end of [val]
  val (fpf_x | x) = (gs)"cairo: illustrating Pascal's theorem"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect0
    (window_, (gsignal)"delete-event", G_CALLBACK (gtk_widget_destroy), (gpointer)null)
  val _sid = g_signal_connect1
    (window, (gsignal)"destroy", G_CALLBACK (gtk_main_quit), (gpointer)null)
//
  val vbox0 = gtk_vbox_new (GFALSE(*homo*), (gint)10(*spacing*))
  val () = gtk_container_add (window, vbox0)
//
  val hbox1 = gtk_hbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (vbox0, hbox1, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref (hbox1)
//
  val darea = gtk_drawing_area_new ()
  val () = the_drawingarea_set (darea)
  val () = gtk_box_pack_start (vbox0, darea, GTRUE, GTRUE, (guint)0)
  val _sid = g_signal_connect
    (darea, (gsignal)"expose-event", G_CALLBACK (fexpose), (gpointer)null)
  val () = g_object_unref (darea)
//
  val hsep = gtk_hseparator_new ()
  val () = gtk_box_pack_start (vbox0, hsep, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref (hsep)
//
  val hbox1 = gtk_hbox_new (GFALSE(*homo*), (gint)5(*spacing*))
  val () = gtk_box_pack_start (vbox0, hbox1, GFALSE, GTRUE, (guint)10)
//
  val (fpf_x | x) = (gs)"_Close"
  val btn_close = gtk_button_new_with_mnemonic (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (btn_close, (gsignal)"clicked", G_CALLBACK(gtk_main_quit), (gpointer_vt)window)
  // end of [val]
  val () = gtk_box_pack_end (hbox1, btn_close, GFALSE, GFALSE, (guint)4)
  val () = g_object_unref (btn_close)
//
  val (fpf_x | x) = (gs)"_Next"
  val btn_next = gtk_button_new_with_mnemonic (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (btn_next, (gsignal)"clicked", G_CALLBACK(fnext), (gpointer)null)
  // end of [val]
  val () = gtk_box_pack_end (hbox1, btn_next, GFALSE, GFALSE, (guint)4)
  val () = g_object_unref (btn_next)
//
  val () = g_object_unref (hbox1)
  val () = g_object_unref (vbox0)
  val () = gtk_widget_show_all (window)
  prval () = fpf_window (window)
  val () = gtk_main ()
} // end of [main1]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$
ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  gtk_init ((int*)&argc, (char***)&argv) ; main1 () ; return ;
} // end of [mainats]
%} // end of [%{$]

(* ****** ****** *)

(* end of [gtkcairopascal.dats] *)
