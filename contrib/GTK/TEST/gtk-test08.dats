(*
**
** A simple GTK example: various arrows
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

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val (fpf_window | window_) = g_object_vref (window) // no-op casting
  val _sid = g_signal_connect0 (
    window_, (gsignal)"destroy", (G_CALLBACK)gtk_main_quit, (gpointer)null
  ) // end of [val]
  val () = gtk_window_set_title (window, "Arrow Buttons")
  val () = gtk_container_set_border_width (window, (guint)10)
//
  val box = gtk_hbox_new (GFALSE, (gint)0)
  val () = gtk_container_set_border_width (box, (guint)10)
  val () = gtk_container_add (window, box)
//
  val button = arrow_button_make (GTK_ARROW_UP, GTK_SHADOW_IN)
  val () = gtk_box_pack_start (box, button, GFALSE, GFALSE, (guint)3)
  val () = g_object_unref (button)
  val button = arrow_button_make (GTK_ARROW_DOWN, GTK_SHADOW_OUT)
  val () = gtk_box_pack_start (box, button, GFALSE, GFALSE, (guint)3)
  val () = g_object_unref (button)
  val button = arrow_button_make (GTK_ARROW_LEFT, GTK_SHADOW_ETCHED_IN)
  val () = gtk_box_pack_start (box, button, GFALSE, GFALSE, (guint)3)
  val () = g_object_unref (button)
  val button = arrow_button_make (GTK_ARROW_RIGHT, GTK_SHADOW_ETCHED_OUT)
  val () = gtk_box_pack_start (box, button, GFALSE, GFALSE, (guint)3)
  val () = g_object_unref (button)
//
  val () = gtk_widget_show (box)
  val () = g_object_unref (box)
//
  val () = gtk_widget_show (window)
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
  gtk_init ((int*)&argc, (char***)&argv) ;
  main1 () ;
  return ;
} // end of [mainats]
%} // end of [%{^]

(* ****** ****** *)

(* end of [gtk-test08.dats] *)
