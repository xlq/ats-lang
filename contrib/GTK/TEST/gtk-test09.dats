(*
**
** A simple GTK example: various labels
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

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect0 (
    window_, (gsignal)"destroy", (G_CALLBACK)gtk_main_quit, (gpointer)null
  ) // end of [val]
  val () = gtk_window_set_title (window, "Label")
//
  val hbox = gtk_hbox_new (GFALSE, (gint)5)
  val () = gtk_container_add (window, hbox)
//
  val vbox = gtk_vbox_new (GFALSE, (gint)5)
  val () = gtk_box_pack_start (hbox, vbox, GFALSE, GFALSE, (guint)0)
  val () = gtk_container_set_border_width (window, (guint)5)
//
  val frame = gtk_frame_new ("Normal Lable")
  val label = gtk_label_new ("This is a Normal label")
  val () = gtk_container_add (frame, label)
  val () = g_object_unref label
  val () = gtk_box_pack_start (vbox, frame, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref frame
//
  val frame = gtk_frame_new ("Multi-line Lable")
  val label = gtk_label_new ("This is a Multi-line label.\nSecond line.\nThird line\n")
  val () = gtk_container_add (frame, label)
  val () = g_object_unref label
  val () = gtk_box_pack_start (vbox, frame, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref frame
//
  val frame = gtk_frame_new ("Left-justified Lable")
  val label = gtk_label_new ("This is a Left-justified\nMulti-line label.\nThird line\n")
  val () = gtk_label_set_justify (label, GTK_JUSTIFY_LEFT)
  val () = gtk_container_add (frame, label)
  val () = g_object_unref label
  val () = gtk_box_pack_start (vbox, frame, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref frame
//
  val frame = gtk_frame_new ("Right-justified Lable")
  val label = gtk_label_new ("This is a Right-justified\nMulti-line label.\nThird line, (j,k)\n")
  val () = gtk_label_set_justify (label, GTK_JUSTIFY_RIGHT)
  val () = gtk_container_add (frame, label)
  val () = g_object_unref label
  val () = gtk_box_pack_start (vbox, frame, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref frame
//
  val () = g_object_unref vbox
//
  val vbox = gtk_vbox_new (GFALSE, (gint)5)
  val () = gtk_box_pack_start (hbox, vbox, GFALSE, GFALSE, (guint)0)
  val frame = gtk_frame_new ("Line Wrapped Lable")
  val label = gtk_label_new ("This is an example of a line-wrapped lable. It \
should not be taking up the entire \
width allocated to it, but automatically \
wraps the words to fit.\
")
  val () = gtk_label_set_line_wrap (label, GTRUE)
  val () = gtk_container_add (frame, label)
  val () = gtk_box_pack_start (vbox, frame, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref label
  val () = g_object_unref frame
//
  val () = g_object_unref vbox
//
  val () = g_object_unref hbox
//
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
  gtk_init ((int*)&argc, (char***)&argv) ;
  main1 () ;
  return ;
} // end of [mainats]
%} // end of [%{^]

(* ****** ****** *)

(* end of [gtk-test09.dats] *)
