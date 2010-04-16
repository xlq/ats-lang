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

fun delete_event {c:cls | c <= GtkWidget} {l:anz}
  (widget: !gobjptr (c, l), event: &GdkEvent, _: gpointer): gboolean = let
  val () = gtk_main_quit ()
in
  GFALSE // delivered!
end // end of [delete_event]

(* ****** ****** *)

%{^
GtkWidget *the_statusbar = NULL;
ats_ptr_type
the_statusbar_get () {
  g_object_ref (G_OBJECT(the_statusbar)); return the_statusbar ;
}
ats_void_type
the_statusbar_set (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (the_statusbar) g_object_unref (G_OBJECT(the_statusbar));
  the_statusbar = x ;
  return ;
} // end of [the_statusbar_set]
%} // end of [%{^] 
extern fun the_statusbar_get (): GtkStatusbar_ptr1 = "the_statusbar_get"
extern fun the_statusbar_set (x: !GtkStatusbar_ptr1): void = "the_statusbar_set"

(* ****** ****** *)

staload PRINTF = "libc/SATS/printf.sats"

#define BUFSZ 128
val countref = ref_make_elt<int> (1)
fun push_item
  (_: ptr, data: uintptr): void = () where {
  var !p_buf with pf_buf = @[byte][BUFSZ]()
  val count = !countref
  val () = !countref := count + 1
  val _ = $PRINTF.snprintf (pf_buf | p_buf, BUFSZ, "Item %d", @(count))
  val statusbar = the_statusbar_get ()
  val () = gtk_statusbar_push (statusbar, (guint)data, (__cast)p_buf) where {
    val data = uint_of_uintptr (data)
    extern castfn __cast (x: ptr):<> string
  }
  val () = g_object_unref (statusbar)
  prval () = pf_buf := bytes_v_of_strbuf_v (pf_buf)
} // end of [push_item]

fun pop_item 
  (_: ptr, data: uintptr): void = () where {
  val statusbar = the_statusbar_get ()
  val data = uint_of_uintptr (data)
  val () = gtk_statusbar_pop (statusbar, (guint)data)
  val () = g_object_unref (statusbar)
} // end of [pop_item]

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_widget_set_size_request (window, (gint)200, (gint)100)
  val () = gtk_window_set_title (window, "GTK Entry Example")
  val _sid = g_signal_connect1
    (window, (gsignal)"delete_event", G_CALLBACK (delete_event), (gpointer)null)
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect0
    (window_, (gsignal)"destroy", G_CALLBACK (gtk_main_quit), (gpointer)null)
//
  val vbox = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_container_add (window, vbox)
//
  val entry = gtk_entry_new ()
  val () = gtk_entry_set_max_length (entry, (gint)50)
  val () = gtk_box_pack_start (vbox, entry, GTRUE, GTRUE, (guint)0)
  val () = gtk_entry_set_text (entry, "hello")
  val () = gtk_widget_show (entry)
  val gp_entry = (gpointer_vt)entry
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
%} // end of [%{^]

(* ****** ****** *)

(* end of [gtk-test12.dats] *)
