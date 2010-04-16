(*
**
** A simple GTK example: statusbars
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
  val () = gtk_window_set_title (window, "GTK Statusbar Example")
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect0
    (window_, (gsignal)"delete_event", G_CALLBACK (delete_event), (gpointer)null)
//
  val vbox = gtk_vbox_new (GFALSE, (gint)1)
  val () = gtk_container_add (window, vbox)
  val () = gtk_widget_show (vbox)
//
  val statusbar = gtk_statusbar_new ()
  val () = the_statusbar_set (statusbar)
  val () = gtk_box_pack_start (vbox, statusbar, GTRUE, GTRUE, guint(0))
  val () = gtk_widget_show (statusbar)
  val context_id = gtk_statusbar_get_context_id (statusbar, "Statusbar Example")
  val context_id = uint_of(context_id)
  val context_id = uintptr_of(context_id)
  val () = g_object_unref (statusbar)
//
  val button = gtk_button_new_with_label ("push item")
  val _sid = g_signal_connect (button, (gsignal)"clicked", G_CALLBACK (push_item), (gpointer)context_id)
  val () = gtk_box_pack_start (vbox, button, GTRUE, GTRUE, guint(2))
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val button = gtk_button_new_with_label ("pop last item")
  val _sid = g_signal_connect (button, (gsignal)"clicked", G_CALLBACK (pop_item), (gpointer)context_id)
  val () = gtk_box_pack_start (vbox, button, GTRUE, GTRUE, guint(2))
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
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

(* end of [gtk-test10.dats] *)
