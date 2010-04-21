(*
**
** A simple GTK example: file selection
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2010
**
*)

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

fun file_ok_sel (
    fs: !GtkFileSelection_ptr1
  ) : void = () where {
  val filename = gtk_file_selection_get_filename (fs)
  val () = printf ("%s\n", @(filename))
} // end of [file_ok_sel]

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val filew = gtk_file_selection_new ("File Selection Test")
  val (fpf_filew | filew_) = g_object_vref (filew)
  val _sid = g_signal_connect0
    (filew_, (gsignal)"destroy", G_CALLBACK(gtk_main_quit), (gpointer)null)
//
  val (fpf_btn | btn) = gtk_file_selection_takeout_ok_button (filew)
  val _sid = g_signal_connect_swapped
    (btn, (gsignal)"clicked", G_CALLBACK(file_ok_sel), filew)
  prval () = fpf_btn (btn)
//
  val (fpf_btn | btn) = gtk_file_selection_takeout_cancel_button (filew)
  val _sid = g_signal_connect_swapped
    (btn, (gsignal)"clicked", G_CALLBACK(gtk_widget_destroy), filew)
  prval () = fpf_btn (btn)
//
  val () = gtk_file_selection_set_filename (filew, "penguin.png")
//
  val () = gtk_widget_show (filew)
  prval () = fpf_filew (filew)
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

(* end of [gtk-test15.dats] *)
