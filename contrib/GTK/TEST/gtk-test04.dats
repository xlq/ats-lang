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

fun callback {c:cls | c <= GtkWidget} {l:anz}
  (widget: !gobjptr (c, l), data: string): void =
  printf ("Hello again: %s was pressed\n", @(data))
// end of [callback]

fun delete_event {c:cls | c <= GtkWidget} {l:anz}
  (widget: !gobjptr (c, l), event: &GdkEvent, _: gpointer): gboolean = let
  val () = gtk_main_quit ()
in
  GFALSE // deletion 
end // end of [delete_event]

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_window_set_title (window, "Hello Buttons!")
//
  val _sid = g_signal_connect (
    window, (gsignal)"delete_event", (G_CALLBACK)delete_event, (gpointer)null
  ) // end of [val]
//
  val () = gtk_container_set_border_width (window, (guint)10U)
//
  val table = gtk_table_new ((guint)2U, (guint)2U, GTRUE)
  val (fpf_table | table_) = g_object_vref (table)
  val () = gtk_container_add (window, table_)
//
  val button = gtk_button_new_with_label ("Button 1")
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", G_CALLBACK(callback), (gpointer)"button 1")
  val (fpf_button | ()) = gtk_table_attach_defaults
    (table, button, (guint)0U, (guint)1U, (guint)0U, (guint)1U)
  val () = gtk_widget_show (button)
  prval () = fpf_button (button)
//
  val button = gtk_button_new_with_label ("Button 2")
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", G_CALLBACK(callback), (gpointer)"button 2")
  val (fpf_button | ()) = gtk_table_attach_defaults
    (table, button, (guint)1U, (guint)2U, (guint)0U, (guint)1U)
  val () = gtk_widget_show (button)
  prval () = fpf_button (button)
//
  val button = gtk_button_new_with_mnemonic ("_Q_u_i_t")
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", G_CALLBACK(delete_event), (gpointer)null)
  val (fpf_button | ()) = gtk_table_attach_defaults
    (table, button, (guint)0U, (guint)2U, (guint)1U, (guint)2U)
  val () = gtk_widget_show (button)
  prval () = fpf_button (button)
//
  val () = gtk_widget_show (table)
  prval () = fpf_table (table)
//
  val () = gtk_widget_show (window)
//
  val () = gtk_main ()
//
  prval () = __leak (window) where {
    extern prfun __leak {a:viewtype} (x: a): void // it is okay after [gtk_main]
  }
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

(* end of [gtk-test04.dats] *)
