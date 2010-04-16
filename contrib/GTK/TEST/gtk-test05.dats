(*
**
** A simple GTK example: box packing
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

fun delete_event {c:cls | c <= GtkWidget} {l:anz}
  (widget: !gobjptr (c, l), event: &GdkEvent, _: gpointer): gboolean = let
  val () = gtk_main_quit ()
in
  GFALSE // deletion 
end // end of [delete_event]

(* ****** ****** *)

fun make_box (
    homo: gboolean
  , spacing: gint
  , expand: gboolean
  , fill: gboolean
  , padding: guint
  ) : GtkHBox_ptr1 = let
  val box = gtk_hbox_new (homo, spacing)
//
  val button = gtk_button_new_with_label ("gtk_box_pack")
  val () = gtk_box_pack_start (box, button, expand, fill, padding)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val button = gtk_button_new_with_label ("(box,")
  val () = gtk_box_pack_start (box, button, expand, fill, padding)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val button = gtk_button_new_with_label ("button,")
  val () = gtk_box_pack_start (box, button, expand, fill, padding)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val label = (if (bool_of)expand then "TRUE," else ",FALSE"): string
  val button = gtk_button_new_with_label (label)
  val () = gtk_box_pack_start (box, button, expand, fill, padding)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val lable = (if (bool_of)fill then "TRUE," else ",FALSE"): string
  val button = gtk_button_new_with_label (label)
  val () = gtk_box_pack_start (box, button, expand, fill, padding)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val (pf_gc, pf_str | p) = tostringf__bufptr ("%u)", @((uint_of)padding))
  val button = gtk_button_new_with_label (label1) where {
    extern castfn __cast {l:addr} (p: ptr l):<> string; val label1 = __cast p
  }
  val () = strbufptr_free @(pf_gc, pf_str | p)
  val () = gtk_box_pack_start (box, button, expand, fill, padding)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
in
  box
end // end of [make_box]
  

(* ****** ****** *)

extern fun main1 (which: int): void = "main1"

implement main1 (which) = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
//
  val _sid = g_signal_connect (
    window, (gsignal)"delete_event", (G_CALLBACK)delete_event, (gpointer)null
  ) // end of [val]
//
  val () = gtk_container_set_border_width (window, (guint)10U)
//
  val box1 = gtk_vbox_new (GFALSE, (gint)0)
//
  val () = case+ 0 of
    | _ when which = 1 => () where {
        val label = gtk_label_new ("gtk_hbox_new (FALSE, 0);")
        val () = gtk_misc_set_alignment (label, (gfloat)0.0, (gfloat)0.0)
        val () = gtk_box_pack_start (box1, label, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (label)
        val () = g_object_unref (label)
//
        val box2 = make_box (GFALSE, (gint)0, GFALSE, GFALSE, (guint)0)
        val () = gtk_box_pack_start (box1, box2, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (box2)
        val () = g_object_unref (box2)
//
        val box2 = make_box (GFALSE, (gint)0, GTRUE, GFALSE, (guint)0)
        val () = gtk_box_pack_start (box1, box2, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (box2)
        val () = g_object_unref (box2)
//
        val box2 = make_box (GFALSE, (gint)0, GTRUE, GTRUE, (guint)0)
        val () = gtk_box_pack_start (box1, box2, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (box2)
        val () = g_object_unref (box2)
//
        val separator = gtk_hseparator_new ()
        val () = gtk_box_pack_start (box1, separator, GFALSE, GTRUE, (guint)5)
        val () = gtk_widget_show (separator)
        val () = g_object_unref (separator)
//
        val label = gtk_label_new ("gtk_hbox_new (TRUE, 0)")
        val () = gtk_misc_set_alignment (label, (gfloat)0.0, (gfloat)0.0)
        val () = gtk_box_pack_start (box1, label, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (label)
        val () = g_object_unref (label)
//
        val box2 = make_box (GTRUE, (gint)0, GTRUE, GFALSE, (guint)0)
        val () = gtk_box_pack_start (box1, box2, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (box2)
        val () = g_object_unref (box2)
//
        val box2 = make_box (GTRUE, (gint)0, GTRUE, GTRUE, (guint)0)
        val () = gtk_box_pack_start (box1, box2, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (box2)
        val () = g_object_unref (box2)
//
        val separator = gtk_hseparator_new ()
        val () = gtk_box_pack_start (box1, separator, GFALSE, GTRUE, (guint)5)
        val () = gtk_widget_show (separator)
        val () = g_object_unref (separator)
      } // end of [which = 1]
    | _ when which = 2 => () where {
        val label = gtk_label_new ("gtk_hbox_new (FALSE, 10)")
        val () = gtk_misc_set_alignment (label, (gfloat)0.0, (gfloat)0.0)
        val () = gtk_box_pack_start (box1, label, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (label)
        val () = g_object_unref (label)
//
        val box2 = make_box (GFALSE, (gint)10, GTRUE, GFALSE, (guint)0)
        val () = gtk_box_pack_start (box1, box2, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (box2)
        val () = g_object_unref (box2)
//
        val box2 = make_box (GFALSE, (gint)10, GTRUE, GTRUE, (guint)0)
        val () = gtk_box_pack_start (box1, box2, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (box2)
        val () = g_object_unref (box2)
//
        val separator = gtk_hseparator_new ()
        val () = gtk_box_pack_start (box1, separator, GFALSE, GTRUE, (guint)5)
        val () = gtk_widget_show (separator)
        val () = g_object_unref (separator)
//
        val label = gtk_label_new ("gtk_hbox_new (FALSE, 0)")
        val () = gtk_misc_set_alignment (label, (gfloat)0.0, (gfloat)0.0)
        val () = gtk_box_pack_start (box1, label, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (label) 
        val () = g_object_unref (label)
//
        val box2 = make_box (GFALSE, (gint)0, GTRUE, GFALSE, (guint)10)
        val () = gtk_box_pack_start (box1, box2, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (box2)
        val () = g_object_unref (box2)
//
        val box2 = make_box (GFALSE, (gint)0, GTRUE, GTRUE, (guint)10)
        val () = gtk_box_pack_start (box1, box2, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (box2)
        val () = g_object_unref (box2)
//
        val separator = gtk_hseparator_new ()
        val () = gtk_box_pack_start (box1, separator, GFALSE, GTRUE, (guint)5)
        val () = gtk_widget_show (separator)
        val () = g_object_unref (separator)
//
      } // end of [which = 2]
    | _ when which = 3 => () where {
        val box2 = make_box (GFALSE, (gint)0, GTRUE, GFALSE, (guint)0)
        val label = gtk_label_new ("end")
        val () = gtk_box_pack_start (box2, label, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (label)
        val () = g_object_unref (label)
        val () = gtk_box_pack_start (box1, box2, GFALSE, GFALSE, (guint)0)
        val () = gtk_widget_show (box2)
        val () = g_object_unref (box2)
//
        val separator = gtk_hseparator_new ()
        val () = gtk_widget_set_size_request (separator, (gint)400, (gint)5)
        val () = gtk_box_pack_start (box1, separator, GFALSE, GTRUE, (guint)5)
        val () = gtk_widget_show (separator)
        val () = g_object_unref (separator)
      } // end of [which = 3]
    | _ => ()
  // end of [case]
//
  val quitbox = gtk_hbox_new (GFALSE, (gint)0)
  val button = gtk_button_new_with_label ("Quit")
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect_swapped0
    (button, (gsignal)"clicked", G_CALLBACK(delete_event), window_)
  val () = gtk_box_pack_start (quitbox, button, GTRUE, GFALSE, (guint)0)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
  val () = gtk_container_add (box1, quitbox)
  val () = gtk_widget_show (quitbox)
  val () = g_object_unref (quitbox)
  val () = gtk_container_add (window, box1)
  val () = gtk_widget_show (box1)
  val () = g_object_unref (box1)
//
  val () = gtk_widget_show (window)
  prval () = fpf_window (window)
//
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
  int which ;
  gtk_init ((int*)&argc, (char***)&argv) ;
  if (argc != 2) {
    fprintf (stderr, "usage: ./test05 <which>, where [which] is 1, 2, or 3\n"); exit(1);
  }
  which = atoi(*((char**)argv + 1));
  main1 (which) ;
  return ;
} // end of [mainats]
%} // end of [%{^]

(* ****** ****** *)

(* end of [gtk-test05.dats] *)
