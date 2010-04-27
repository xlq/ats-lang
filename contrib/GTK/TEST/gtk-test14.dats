(*
**
** A simple GTK example: color selection dialog
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

%{^
GtkWidget *the_drawingarea = NULL;
ats_ptr_type
the_drawingarea_get () {
  g_object_ref (G_OBJECT(the_drawingarea)); return the_drawingarea ;
}
ats_void_type
the_drawingarea_set (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (the_drawingarea) g_object_unref (G_OBJECT(the_drawingarea));
  the_drawingarea = x ;
  return ;
} // end of [the_drawingarea_set]
%} // end of [%{^] 
extern fun the_drawingarea_get (): GtkDrawingArea_ptr1 = "the_drawingarea_get"
extern fun the_drawingarea_set (x: !GtkDrawingArea_ptr1): void = "the_drawingarea_set"

(* ****** ****** *)

%{^
GtkWidget *the_colorseldlg = NULL;
ats_ptr_type
the_colorseldlg_get () {
  if (the_colorseldlg) g_object_ref (G_OBJECT(the_colorseldlg));
  return the_colorseldlg ;
} // end of [...]
ats_void_type
the_colorseldlg_set (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (the_colorseldlg) g_object_unref (G_OBJECT(the_colorseldlg));
  the_colorseldlg = x ;
  return ;
} // end of [the_colorseldlg_set]
%} // end of [%{^] 
extern fun the_colorseldlg_get (): GtkColorSelectionDialog_ptr0 = "the_colorseldlg_get"
extern fun the_colorseldlg_set (x: !GtkColorSelectionDialog_ptr1): void = "the_colorseldlg_set"

(* ****** ****** *)

fun cb_color_changed
  (colorsel: !GtkColorSelection_ptr1): void = () where {
  var ncolor: GdkColor
  val () = gtk_color_selection_get_current_color (colorsel, ncolor)
  val darea = the_drawingarea_get ()
  val () = gtk_widget_modify_bg (darea, GTK_STATE_NORMAL, ncolor)
  val () = g_object_unref (darea)
} // end of [cb_color_changed]

(* ****** ****** *)

%{^
GdkColor the_color ;
ATSinline()
ats_ptr_type the_color_takeout () { return &the_color ; }
%} // end of [%{^]
extern fun the_color_takeout ()
  : [l:addr] (GdkColor @ l, GdkColor @ l -<lin,prf> void | ptr l) = "the_color_takeout"
// end of [the_color_takeout]

(* ****** ****** *)

overload gint with gint_of_GtkResponseType

fun area_event (
    _: ptr, event: &GdkEvent, data: gpointer
  ) : gboolean = let
  val _type = event.type
in
  case+ 0 of
  | _ when (_type = GDK_BUTTON_PRESS) => let
      var colorseldlg = the_colorseldlg_get ()
(*
      val p_colorseldlg = ptr_of_gobjptr (colorseldlg)
      val () = (print "p_colorseldlg(0) = "; print p_colorseldlg; print_newline ())
*)
      val () = if
        :(colorseldlg: GtkColorSelectionDialog_ptr1) =>
        g_object_is_null (colorseldlg) then let
        val () = g_object_free_null colorseldlg
        val () = colorseldlg := gtk_color_selection_dialog_new ("Select BG Color")
        val () = the_colorseldlg_set (colorseldlg)
      in
        // nothing
      end // end of [if]
(*
      val p_colorseldlg = ptr_of_gobjptr (colorseldlg)
      val () = (print "p_colorseldlg(1) = "; print p_colorseldlg; print_newline ())
*)
      val (fpf_colorsel | colorsel) =
        gtk_color_selection_dialog_takeout_colorsel (colorseldlg)
      // end of [val]
//
      val (pf_color, fpf_color | p_color) = the_color_takeout ()
//
      val () = gtk_color_selection_set_previous_color (colorsel, !p_color)
      val () = gtk_color_selection_set_current_color (colorsel, !p_color)
      val () = gtk_color_selection_set_has_palette (colorsel, GTRUE)
//
      val _sid = g_signal_connect
        (colorsel, (gsignal)"color_changed", G_CALLBACK(cb_color_changed), (gpointer)null)
      val response = gtk_dialog_run (colorseldlg)
      val () = case+ 0 of
        | _ when (response = (gint)GTK_RESPONSE_OK) =>
            gtk_color_selection_get_current_color (colorsel, !p_color)
        | _ => () where {
            val darea = the_drawingarea_get ()
            val () = gtk_widget_modify_bg (darea, GTK_STATE_NORMAL, !p_color)
            val () = g_object_unref (darea)
          } // end of [_]
      prval () = fpf_color (pf_color)
      prval () = fpf_colorsel (colorsel)
      val () = gtk_widget_hide (colorseldlg)
      val () = g_object_unref (colorseldlg)
    in
      GTRUE
    end // end of [GDK_BUTTON_PRESS]
  | _ => GFALSE // the event is not handled
end // end of [area_event]

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_window_set_title (window, "Color Selection Test")
  val () = gtk_window_set_resizeable (window, GTRUE)
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect0 (
    window_, (gsignal)"destroy", G_CALLBACK(gtk_main_quit), (gpointer)null
  ) // end of [val]
  val darea = gtk_drawing_area_new ()
  val () = the_drawingarea_set (darea)
  val (pf_color, fpf_color | p_color) = the_color_takeout ()
  val () = gdk_color3_set (!p_color, 0U, 65535U, 0U)
  val () = gtk_widget_modify_bg (darea, GTK_STATE_NORMAL, !p_color)
  prval () = fpf_color (pf_color)
  val () = gtk_widget_set_size_request (darea, (gint)200, (gint)200)
  extern castfn gint (x: GdkEventMask):<> gint
  val () = gtk_widget_set_events (darea, (gint)GDK_BUTTON_PRESS_MASK)
  val _sid = g_signal_connect (darea, (gsignal)"event", G_CALLBACK (area_event), (gpointer)null)
//
  val () = gtk_container_add (window, darea)
  val () = gtk_widget_show (darea)
  val () = g_object_unref (darea)
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

(* end of [gtk-test14.dats] *)
