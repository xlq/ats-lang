(*
**
** A simple GTK example: table packing
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2010
**
*)

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

fun arrow_button_make
  (arrow_type: GtkArrowType, shadow_type: GtkShadowType)
  : GtkButton_ptr1 = let
  val button = gtk_button_new ()
  val arrow = gtk_arrow_new (arrow_type, shadow_type)
  val () = gtk_container_add (button, arrow)
  val () = gtk_widget_show arrow
  val () = g_object_unref (arrow)
  val () = gtk_widget_show button
in
  button
end // end of [array_button_make]  

(* ****** ****** *)

fun scale_set_default_values
  {c:cls | c <= GtkScale} {l:anz}
  (scale: !gobjptr (c, l)): void = () where {
  val () = gtk_range_set_update_policy (scale, GTK_UPDATE_CONTINUOUS)
  val () = gtk_scale_set_digits (scale, (gint)1)
  val () = gtk_scale_set_value_pos (scale, GTK_POS_TOP)
  val () = gtk_scale_set_draw_value (scale, GTRUE)
} // end of [scale_set_default_values]

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val _sid = g_signal_connect (
    window, (gsignal)"destroy", (G_CALLBACK)gtk_main_quit, (gpointer)null
  ) // end of [val]
  val () = gtk_window_set_title (window, "Range Controls")
//
  val box1 = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_widget_show (box1)
  val () = gtk_container_add (window, box1)
//
  val box2 = gtk_hbox_new (GFALSE, (gint)10)
  val () = gtk_widget_show (box2)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val () = gtk_box_pack_start (box1, box2, GTRUE, GTRUE, (guint)0)
//
  val adj1 = gtk_adjustment_new (
    (gdouble)0.0, (gdouble)0.0, (gdouble)101.0, (gdouble)0.1, (gdouble)1.0, (gdouble)1.0
  ) // end of [val]
//
  val vscale = gtk_vscale_new (adj1)
  val () = scale_set_default_values (vscale)
  val () = gtk_box_pack_start (box2, vscale, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (vscale)
  val () = g_object_unref (vscale)
//
  val box3 = gtk_vbox_new (GFALSE, (gint)10)
  val () = gtk_widget_show (box3)
  val () = gtk_box_pack_start (box2, box3, GTRUE, GTRUE, (guint)0)
//
  val hscale = gtk_hscale_new (adj1)
  val () = gtk_widget_set_size_request (hscale, (gint)200, (gint)~1)
  val () = gtk_box_pack_start (box3, hscale, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (hscale)
  val () = g_object_unref (hscale)
//
  val () = g_object_unref (adj1)
//
  val () = g_object_unref (box3)
  val () = g_object_unref (box2)
  val () = g_object_unref (box1)
//
  val () = gtk_widget_show (window)
  val () = gtk_main ()
//
  extern prfun __leak {a:viewtype} (x: a): void // it is okay after [gtk_main]
  prval () = __leak (window)
} // end of [main1]

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
%} // end of [%{^]

(* ****** ****** *)

(* end of [gtk-test07.dats] *)
