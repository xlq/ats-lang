(*
**
** A simple GTK example: text entries
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

staload _(*anon*) = "prelude/DATS/reference.dats"

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
  val () = gtk_widget_set_size_request (window, (gint)200, (gint)100)
  val () = gtk_window_set_title (window, "GTK Entry Example")
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect0
    (window_, (gsignal)"destroy", G_CALLBACK (gtk_main_quit), (gpointer)null)
//
  val vbox = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_container_add (window, vbox)
//
  val entry = gtk_entry_new () // HX: it seems to be grabbed by default!
  val gp_entry = (gpointer_vt)entry
  val () = gtk_entry_set_max_length (entry, (gint)50)
  val _sid = g_signal_connect (
    entry, (gsignal)"activate", G_CALLBACK (cb), gp_entry
  ) where {
    val cb = lam (
      _: ptr, entry: !GtkEntry_ptr1
    ) : void => () where {
      val (stamp | text) = gtk_entry_get_text (entry)
      prval () = stamped_decode {string} (text)
      val () = printf (
        "Entry contexts: %s\n", @(__x)
      ) where {
        extern castfn __id (x: !string):<> string; val __x = __id text
      } // end of [val]
      prval () = stamped_encode {string} (text)
      prval () = stamp_forfeit (stamp, text)
    } // end of [val]
  }
  val () = gtk_box_pack_start (vbox, entry, GTRUE, GTRUE, (guint)0)
  val () = gtk_entry_set_text (entry, "hello")
  val () = gtk_widget_show (entry)
  val () = g_object_unref (entry)
//
  val hbox = gtk_hbox_new (GFALSE, (gint)0)
  val () = gtk_container_add (vbox, hbox)
//
  val check = gtk_check_button_new_with_label ("Editable")
  val _sid = g_signal_connect
    (check, (gsignal)"toggled", G_CALLBACK cb, gp_entry) where {
    val cb = lam (
        x1: !GtkToggleButton_ptr1, x2: !GtkEntry_ptr1
      ) : void => () where {
      val () = gtk_entry_set_editable (x2, gtk_toggle_button_get_active (x1))
    } // end of [cb]
  } // end of [val]
  val () = gtk_box_pack_start (hbox, check, GTRUE, GTRUE, (guint)0)
  val () = gtk_toggle_button_set_active (check, GTRUE)
  val () = gtk_widget_show (check)
  val () = g_object_unref (check)
//
  val check = gtk_check_button_new_with_label ("Visible")
  val _sid = g_signal_connect
    (check, (gsignal)"toggled", G_CALLBACK cb, gp_entry) where {
    val cb = lam (
        x1: !GtkToggleButton_ptr1, x2: !GtkEntry_ptr1
      ) : void => () where {
      val () = gtk_entry_set_visibility (x2, gtk_toggle_button_get_active (x1))
    } // end of [cb]
  } // end of [val]
  val () = gtk_box_pack_start (hbox, check, GTRUE, GTRUE, (guint)0)
  val () = gtk_toggle_button_set_active (check, GTRUE)
  val () = gtk_widget_show (check)
  val () = g_object_unref (check)
//
  val () = gtk_widget_show (hbox)
  val () = g_object_unref (hbox)
//
  val button = gtk_button_new_from_stock (GTK_STOCK_CLOSE)
  val _sid = g_signal_connect_swapped
    (button, (gsignal)"clicked", G_CALLBACK (gtk_widget_destroy), window)
  val () = gtk_box_pack_start (vbox, button, GTRUE, GTRUE, (guint)0)
//
  val () = GTK_WIDGET_SET_FLAGS (button, GTK_CAN_DEFAULT)
  val () = gtk_widget_grab_default (button)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val () = gtk_widget_show (vbox)
  val () = g_object_unref (vbox)
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
%} // end of [%{$]

(* ****** ****** *)

(* end of [gtk-test12.dats] *)
