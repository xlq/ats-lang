(*
**
** A simple GTK example: spin buttons
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
GtkWidget *the_spinner1 = NULL;
ats_ptr_type
the_spinner1_get () {
  g_object_ref (G_OBJECT(the_spinner1)); return the_spinner1 ;
}
ats_void_type
the_spinner1_set (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (the_spinner1) g_object_unref (G_OBJECT(the_spinner1));
  the_spinner1 = x ;
  return ;
} // end of [the_spinner1_set]
%} // end of [%{^] 
extern fun the_spinner1_get (): GtkSpinButton_ptr1 = "the_spinner1_get"
extern fun the_spinner1_set (x: !GtkSpinButton_ptr1): void = "the_spinner1_set"

(* ****** ****** *)

fun toggle_snap (
    toggle: !GtkToggleButton_ptr1, spin: !GtkSpinButton_ptr1
  ) : void = () where {
 val active = gtk_toggle_button_get_active (toggle)
 val () = gtk_spin_button_set_snap_to_ticks (spin, active)
} // end of [toggle_snap]

(* ****** ****** *)

fun toggle_numeric (
    toggle: !GtkToggleButton_ptr1, spin: !GtkSpinButton_ptr1
  ) : void = () where {
 val active = gtk_toggle_button_get_active (toggle)
 val () = gtk_spin_button_set_numeric (spin, active)
} // end of [toggle_numeric]

(* ****** ****** *)

fun change_digits (
    _: ptr, spin: !GtkSpinButton_ptr1
  ) : void = () where {
  val spinner1 = the_spinner1_get ()
  val n = gtk_spin_button_get_value (spin)
  val n = uint_of(int_of(double_of(n)))
  val () = gtk_spin_button_set_digits (spinner1, (guint)n)
  val () = g_object_unref (spinner1)
} // end of [change_digits]

(* ****** ****** *)

%{^
GtkWidget *the_val_label = NULL;
ats_ptr_type
the_val_label_get () {
  g_object_ref (G_OBJECT(the_val_label)); return the_val_label ;
}
ats_void_type
the_val_label_set (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (the_val_label) g_object_unref (G_OBJECT(the_val_label));
  the_val_label = x ;
  return ;
} // end of [the_val_label_set]
%} // end of [%{^] 
extern fun the_val_label_get (): GtkLabel_ptr1 = "the_val_label_get"
extern fun the_val_label_set (x: !GtkLabel_ptr1): void = "the_val_label_set"

(* ****** ****** *)

#define BUFSZ 32
staload PRINTF = "libc/SATS/printf.sats"

extern fun snprintf0
  (buf: ptr, sz: int, fmt: string, v: int): int = "#snprintf"
// end of [snprintf0]

extern fun snprintf1
  (buf: ptr, sz: int, fmt: string, np: uint, v: double): int = "#snprintf"
// end of [snprintf1]

fun get_value
  (_: ptr, tag: uintptr): void = () where {
  val tag = (uint_of_uintptr)tag
  var !p_buf with pf_buf = @[byte][BUFSZ]()  
  val spinner1 = the_spinner1_get ()
  val val_label = the_val_label_get ()
  val value = gtk_spin_button_get_value (spinner1)
  val value = double_of(value)
  val _ = (case+ 0 of
    | _ when tag = 0U => () where {
        // val _ = $PRINTF.snprintf (pf_buf | p_buf, BUFSZ, "%d", @((int_of)value))
        val _ = snprintf0 (p_buf, BUFSZ, "%d", int_of(value))
      } // end of [tag = 1]
    | _ => () where {
        // val _ = $PRINTF.snprintf (pf_buf | p_buf, BUFSZ, "%f", @(value))
        val np = gtk_spin_button_get_digits (spinner1)
        val np = (uint_of(np))
        val _ = snprintf1 (p_buf, BUFSZ, "%0.*f", np, value)
      } // end of [_]
  ) // end of [val]
  val () = gtk_label_set_text (val_label, (__cast)p_buf) where {
    extern castfn __cast (x: ptr):<> string
  } // end of [val]
  val () = g_object_unref (val_label)
  val () = g_object_unref (spinner1)
} // end of [get_value]

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect0 (
    window_, (gsignal)"destroy", G_CALLBACK(gtk_main_quit), (gpointer)null
  ) // end of [val]
//
  // creating the main vbox
  val vbox0 = gtk_vbox_new (GFALSE(*homo*), (gint)0)
  val () = gtk_container_set_border_width (vbox0, (guint)10)
  val () = gtk_container_add (window, vbox0)
//
  val frame = gtk_frame_new ("Not Accelerated")
  val () = gtk_box_pack_start (vbox0, frame, GTRUE, GTRUE, (guint)0)
  val vbox = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_container_set_border_width (vbox, (guint)5)
  val () = gtk_container_add (frame, vbox)
//
  val hbox = gtk_hbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (vbox, hbox, GTRUE, GTRUE, (guint)5)
//
  val vbox2 = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (hbox, vbox2, GTRUE, GTRUE, (guint)5)
  val label = gtk_label_new ("Day: ")
  val () = gtk_misc_set_alignment (label, (gfloat)0.0, (gfloat)0.5)
  val () = gtk_box_pack_start (vbox2, label, GTRUE, GTRUE, (guint)5)
  val () = gtk_widget_show (label)
  val () = g_object_unref (label)
  val adj = gtk_adjustment_new (1.0, 1.0, 31.0, 1.0, 5.0, 0.0)
  val spinner = gtk_spin_button_new (adj, (gdouble)0.0, (guint)0)
  val () = gtk_spin_button_set_wrap (spinner, GTRUE)
  val () = gtk_box_pack_start (vbox2, spinner, GFALSE, GTRUE, (guint)0)
  val () = gtk_widget_show (spinner)
  val () = g_object_unref (spinner)
  val () = g_object_unref (adj)
  val () = gtk_widget_show (vbox2)
  val () = g_object_unref (vbox2)
//
  val vbox2 = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (hbox, vbox2, GTRUE, GTRUE, (guint)5)
  val label = gtk_label_new ("Month: ")
  val () = gtk_misc_set_alignment (label, (gfloat)0.0, (gfloat)0.5)
  val () = gtk_box_pack_start (vbox2, label, GTRUE, GTRUE, (guint)5)
  val () = gtk_widget_show (label)
  val () = g_object_unref (label)
  val adj = gtk_adjustment_new (1.0, 1.0, 12.0, 1.0, 5.0, 0.0)
  val spinner = gtk_spin_button_new (adj, (gdouble)0.0, (guint)0)
  val () = gtk_spin_button_set_wrap (spinner, GTRUE)
  val () = gtk_box_pack_start (vbox2, spinner, GFALSE, GTRUE, (guint)0)
  val () = gtk_widget_show (spinner)
  val () = g_object_unref (spinner)
  val () = g_object_unref (adj)
  val () = gtk_widget_show (vbox2)
  val () = g_object_unref (vbox2)
//
  val vbox2 = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (hbox, vbox2, GTRUE, GTRUE, (guint)5)
  val label = gtk_label_new ("Year: ")
  val () = gtk_misc_set_alignment (label, (gfloat)0.0, (gfloat)0.5)
  val () = gtk_box_pack_start (vbox2, label, GTRUE, GTRUE, (guint)5)
  val () = gtk_widget_show (label)
  val () = g_object_unref (label)
  val adj = gtk_adjustment_new (1998.0, 0.0, 2100.0, 1.0, 100.0, 0.0)
  val spinner = gtk_spin_button_new (adj, (gdouble)0.0, (guint)0)
  val () = gtk_spin_button_set_wrap (spinner, GTRUE)
  val () = gtk_widget_set_size_request (spinner, (gint)55, (gint)~1)
  val () = gtk_box_pack_start (vbox2, spinner, GFALSE, GTRUE, (guint)0)
  val () = gtk_widget_show (spinner); val () = g_object_unref (spinner)
  val () = g_object_unref (adj)
  val () = gtk_widget_show (vbox2); val () = g_object_unref (vbox2)
//
  val () = gtk_widget_show (hbox); val () = g_object_unref (hbox)
  val () = gtk_widget_show (vbox); val () = g_object_unref (vbox)
  val () = gtk_widget_show (frame); val () = g_object_unref (frame)
//
  val frame = gtk_frame_new ("Accelerated")
  val () = gtk_box_pack_start (vbox0, frame, GTRUE, GTRUE, (guint)0)
  val vbox = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_container_set_border_width (vbox, (guint)5)
  val () = gtk_container_add (frame, vbox)
//
  val hbox = gtk_hbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (vbox, hbox, GFALSE, GTRUE, (guint)5)
//
  val vbox2 = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (hbox, vbox2, GTRUE, GTRUE, (guint)5)
  val label = gtk_label_new ("Value: ")
  val () = gtk_misc_set_alignment (label, (gfloat)0.0, (gfloat)0.5)
  val () = gtk_box_pack_start (vbox2, label, GFALSE, GTRUE, (guint)0)
  val () = gtk_widget_show (label); val () = g_object_unref (label)
  val adj = gtk_adjustment_new (0.0, ~10000.0, 10000.0, 0.5, 100.0, 0.0)
  val spinner1 = gtk_spin_button_new (adj, (gdouble)100.0, (guint)2)
  val () = the_spinner1_set (spinner1)
  val gp_spinner1 = (gpointer_vt)spinner1
  val () = gtk_box_pack_start (vbox2, spinner1, GFALSE, GTRUE, (guint)0)
  val () = gtk_spin_button_set_wrap (spinner1, GTRUE)
  val () = gtk_widget_set_size_request (spinner1, (gint)100, (gint)~1)
  val () = gtk_widget_show (spinner1); val () = g_object_unref (spinner1)
  val () = gtk_widget_show (vbox2); val () = g_object_unref (vbox2)
  val () = g_object_unref (adj)
//
  val vbox2 = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (hbox, vbox2, GTRUE, GTRUE, (guint)5)
  val label = gtk_label_new ("Digits: ")
  val () = gtk_misc_set_alignment (label, (gfloat)0.0, (gfloat)0.5)
  val () = gtk_box_pack_start (vbox2, label, GFALSE, GTRUE, (guint)0)
  val () = gtk_widget_show (label); val () = g_object_unref (label)
  val adj = gtk_adjustment_new (2.0, 1.0, 5.0, 1.0, 1.0, 0.0)
  val spinner2 = gtk_spin_button_new (adj, (gdouble)0.0, (guint)0)
  val () = gtk_box_pack_start (vbox2, spinner2, GFALSE, GTRUE, (guint)0)
  val () = gtk_spin_button_set_wrap (spinner2, GTRUE)
  val () = gtk_widget_set_size_request (spinner2, (gint)100, (gint)~1)
  val gp_spinner2 = (gpointer_vt)spinner2
  val _sid = g_signal_connect
    (adj, (gsignal)"value_changed", G_CALLBACK(change_digits), gp_spinner2)
  val () = gtk_widget_show (spinner2); val () = g_object_unref (spinner2)
  val () = gtk_widget_show (vbox2); val () = g_object_unref (vbox2)
  val () = g_object_unref (adj)
  val () = gtk_widget_show (hbox); val () = g_object_unref (hbox)
//
  val hbox = gtk_hbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (vbox, hbox, GFALSE, GTRUE, (guint)5)
  val () = g_object_unref (hbox)
//
  val button = gtk_check_button_new_with_label ("Snap to 0.5-ticks")
  val () = gtk_box_pack_start (vbox, button, GTRUE, GTRUE, (guint)0)
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", (G_CALLBACK)toggle_snap, gp_spinner1)
  val () = gtk_toggle_button_set_active (button, GTRUE)
  val () = gtk_widget_show (button); val () = g_object_unref (button)
//
  val button = gtk_check_button_new_with_label ("Numeric only input mode")
  val () = gtk_box_pack_start (vbox, button, GTRUE, GTRUE, (guint)0)
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", (G_CALLBACK)toggle_numeric, gp_spinner1)
  val () = gtk_toggle_button_set_active (button, GTRUE)
  val () = gtk_widget_show (button); val () = g_object_unref (button)
//
  val val_label = gtk_label_new ("")
  val () = the_val_label_set (val_label)
  val gp_val_label = (gpointer_vt)val_label
  val hbox = gtk_hbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (vbox, hbox, GFALSE, GTRUE, (guint)5)
  val button = gtk_button_new_with_label ("Value as Int")
  val () = gtk_box_pack_start (hbox, button, GTRUE, GTRUE, (guint)5)
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", (G_CALLBACK)get_value, (gpointer)null)
  val () = gtk_widget_show (button); val () = g_object_unref (button)
  val button = gtk_button_new_with_label ("Value as Float")
  val () = gtk_box_pack_start (hbox, button, GTRUE, GTRUE, (guint)5)
  val _1 = intptr_of(1)
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", (G_CALLBACK)get_value, (gpointer)_1)
  val () = gtk_widget_show (button); val () = g_object_unref (button)
  val () = gtk_widget_show (hbox); val () = g_object_unref (hbox)
  val () = gtk_box_pack_start (vbox, val_label, GTRUE, GTRUE, (guint)0)
  val () = gtk_label_set_text (val_label, "0")
  val () = gtk_widget_show (val_label); val () = g_object_unref (val_label)
//
  val () = gtk_widget_show (vbox); val () = g_object_unref (vbox)
  val () = gtk_widget_show (frame); val () = g_object_unref (frame)
//
// Close button
//
  val hbox = gtk_hbox_new (GFALSE, (gint)0)
  val () = gtk_box_pack_start (vbox0, hbox, GFALSE, GTRUE, (guint)0)
  val button = gtk_button_new_with_label ("Close")
  val () = gtk_box_pack_start (hbox, button, GTRUE, GTRUE, (guint)5)
  val _sid = g_signal_connect_swapped
    (button, (gsignal)"clicked", G_CALLBACK (gtk_widget_destroy), window)
  val () = gtk_widget_show (button); val button = g_object_unref (button)
  val () = gtk_widget_show (hbox); val () = g_object_unref (hbox)
//
  val () = gtk_widget_show (vbox0); val () = g_object_unref (vbox0)
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

(* end of [gtk-test13.dats] *)
