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

fun close_application
  {c:cls | c <= GtkWidget} {l:anz}
  (widget: !gobjptr (c, l), event: &GdkEvent, data: gpointer): gboolean = let
  val () = gtk_main_quit ()
in
  GFALSE // deletion 
end // end of [close_application]

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val _sid = g_signal_connect (
    window, (gsignal)"delete_event", (G_CALLBACK)close_application, (gpointer)null
  ) // end of [val]
  val () = gtk_window_set_title (window, "radio buttons")
//
  val () = gtk_container_set_border_width (window, (guint)0)
//
  val box1 = gtk_vbox_new (GFALSE, (gint)0)
  val (fpf_box1 | box1_) = g_object_vref (box1)
  val () = gtk_container_add (window, box1_)
//
  val box2 = gtk_vbox_new (GFALSE, (gint)10)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val (fpf_box2 | box2_) = g_object_vref (box2)
  val () = gtk_box_pack_start (box1, box2_, GTRUE, GTRUE, (guint)0)
//
  val G_SLIST_NULL = g_slist_new_nil ()
  val button1 = gtk_radio_button_new_with_label (G_SLIST_NULL, "button1")
  val () = g_slist_free_nil (G_SLIST_NULL)
  val (fpf_button1 | button1_) = g_object_vref (button1)
  val () = gtk_box_pack_start (box2, button1_, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (button1)
  val (fpf_group | group) = gtk_radio_button_get_group (button1)
  prval () = fpf_button1 (button1)
//
  val button2 = gtk_radio_button_new_with_label (group, "button2")
  prval () = fpf_group (group)
  val () = gtk_toggle_button_set_active (button2, GTRUE)
  val (fpf_button2 | button2_) = g_object_vref (button2)
  val () = gtk_box_pack_start (box2, button2_, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (button2)
//
  val button3 = gtk_radio_button_new_with_label_from_widget (button2, "button3")
  prval () = fpf_button2 (button2)
  val (fpf_button3 | button3_) = g_object_vref (button3)
  val () = gtk_box_pack_start (box2, button3_, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (button3)
  prval () = fpf_button3 (button3)
//
  val () = gtk_widget_show (box2)
  prval () = fpf_box2 (box2)
//
  val sep = gtk_hseparator_new ()
  val (fpf_sep | sep_) = g_object_vref (sep)
  val () = gtk_box_pack_start (box1, sep_, GFALSE, GTRUE, (guint)0)
  val () = gtk_widget_show (sep)
  prval () = fpf_sep (sep)
//
  val box2 = gtk_vbox_new (GFALSE, (gint)10)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val (fpf_box2 | box2_) = g_object_vref (box2)
  val () = gtk_box_pack_start (box1, box2_, GFALSE, GTRUE, (guint)0)  
//
  val button = gtk_button_new_with_label ("close")
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect_swapped0
    (button, (gsignal)"clicked", G_CALLBACK(close_application), window_)
  val (fpf_button | button_) = g_object_vref (button)
  val () = gtk_box_pack_start (box2, button_, GTRUE, GTRUE, (guint)0)
  val () = GTK_WIDGET_SET_FLAGS (button, GTK_CAN_DEFAULT)
  val () = gtk_widget_grab_default (button)
  val () = gtk_widget_show (button)
  prval () = fpf_button (button)
//
  val () = gtk_widget_show (box2)
  prval () = fpf_box2 (box2)
//
  val () = gtk_widget_show (box1)
  prval () = fpf_box1 (box1)
//
  val () = gtk_widget_show (window)
  prval () = fpf_window (window)
//
  val () = gtk_main ()
//
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

(* end of [gtk-test06.dats] *)
