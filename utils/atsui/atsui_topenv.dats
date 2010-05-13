(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2010-201? Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: April 2010

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/pango/SATS/pango.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"
extern fun gdk_cairo_create
  {c:cls | c <= GdkDrawable} {l:agz} (widget: !gobjref (c, l)): cairo_ref1
  = "#gdk_cairo_create"
// end of [gdk_cairo_create]

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"
stadef srcwin = $SWL.srcwin

(* ****** ****** *)

staload "atsui_topenv.sats"
macdef gs = gstring_of_string
overload gint with gint_of_GtkResponseType

(* ****** ****** *)

%{^

/* ****** ****** */

ATSUItopenv theATSUItopenv ;

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_topwin () { return theATSUItopenv.topwin ; }
// end of [atsui_topenv_get_topwin]

ats_void_type
atsui_topenv_initset_topwin
  (ats_ptr_type win) {
  if (theATSUItopenv.topwin != (GtkWindow*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_topwin] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.topwin = (GtkWindow*)win ;
} // end of [atsui_topenv_initset_topwin]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_aclgrp () { return theATSUItopenv.aclgrp ; }
// end of [atsui_topenv_get_aclgrp]

ats_void_type
atsui_topenv_initset_aclgrp
  (ats_ptr_type aclgrp) {
  if (theATSUItopenv.aclgrp != (GtkAccelGroup*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_aclgrp] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.aclgrp = (GtkAccelGroup*)aclgrp ;
} // end of [atsui_topenv_initset_aclgrp]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_vbox0 () { return theATSUItopenv.vbox0 ; }
// end of [atsui_topenv_get_vbox0]

ats_void_type
atsui_topenv_initset_vbox0
  (ats_ptr_type vbox0) {
  if (theATSUItopenv.vbox0 != (GtkVBox*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_vbox0] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.vbox0 = (GtkVBox*)vbox0 ;
} // end of [atsui_topenv_initset_vbox0]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_container_source () {
  return theATSUItopenv.container_source ;
} // end of [atsui_topenv_get_container_source]

ats_void_type
atsui_topenv_initset_container_source
  (ats_ptr_type x) {
  if (theATSUItopenv.container_source != (GtkFrame*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_container_source] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.container_source = (GtkFrame*)x ;
} // end of [atsui_topenv_initset_container_source]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_textview_source () {
  return theATSUItopenv.textview_source ;
} // end of [atsui_topenv_get_textview_source]

static
int topenv_textview_source_initset_flag = 0 ;

ats_void_type
atsui_topenv_initset_textview_source
  (ats_ptr_type x) {
  topenv_textview_source_initset_flag = 1 ;
  theATSUItopenv.textview_source = (GtkTextView*)x ;
} // end of [atsui_topenv_initset_textview_source]

ats_int_type
atsui_topenv_textview_source_initset_flag_get
  () { return topenv_textview_source_initset_flag ; }
// end of [atsui_topenv_textview_source_initset_flag_get]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_container_output () {
  return theATSUItopenv.container_output ;
} // end of [atsui_topenv_get_container_output]

ats_void_type
atsui_topenv_initset_container_output
  (ats_ptr_type x) {
  if (theATSUItopenv.container_output != (GtkContainer*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_container_output] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.container_output = (GtkContainer*)x ;
} // end of [atsui_topenv_initset_container_output]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_textview_output () {
  return theATSUItopenv.textview_output ;
} // end of [atsui_topenv_get_textview_output]

ats_void_type
atsui_topenv_initset_textview_output
  (ats_ptr_type x) {
  if (theATSUItopenv.textview_output != (GtkTextView*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_textview_output] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.textview_output = (GtkTextView*)x ;
} // end of [atsui_topenv_initset_textview_output]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_statusbar () {
  return theATSUItopenv.statusbar ;
} // end of [atsui_topenv_get_statusbar]

ats_void_type
atsui_topenv_initset_statusbar
  (ats_ptr_type x) {
  if (theATSUItopenv.statusbar != (GtkStatusbar*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_statusbar] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.statusbar = (GtkStatusbar*)x ;
} // end of [atsui_topenv_initset_statusbar]

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

%{^
GtkWidget *the_drawarea_welcome = NULL;
ats_ptr_type
the_drawarea_welcome_get () {
  GtkWidget *x = the_drawarea_welcome;
  if (x == NULL) {
    fprintf (stderr, "exit(the_drawarea_welcome_get)\n"); exit(1);
  } // end of [if]
  the_drawarea_welcome = NULL; return x ;
} // end of [the_drawarea_welcome_get]
ats_void_type
the_drawarea_welcome_set (ats_ptr_type x) {
  if (the_drawarea_welcome != NULL) {
    fprintf (stderr, "exit(the_drawarea_welcome_set)\n"); exit(1);
  } // end of [if]
  the_drawarea_welcome = x ; return ;
} // end of [the_drawarea_welcome_set]
%} // end of [%{^] 

extern
fun the_drawarea_welcome_get
  (): GtkDrawingArea_ref1 = "the_drawarea_welcome_get"
extern
fun the_drawarea_welcome_set
  (x: GtkDrawingArea_ref1): void = "the_drawarea_welcome_set"
fun the_drawarea_welcome_fini (): void = () where {
  val darea = the_drawarea_welcome_get (); val () = gtk_widget_destroy (darea)
} // end of [the_drawarea_welcome_fini]

(* ****** ****** *)

//

extern
fun topenv_initset_aclgrp (x: GtkAccelGroup_ref1): void
  = "atsui_topenv_initset_aclgrp"
// end of [topenv_initset_aclgrp]

//

extern
fun topenv_initset_vbox0 (x: GtkVBox_ref1): void
  = "atsui_topenv_initset_vbox0"
// end of [topenv_initset_vbox0]

/* ****** ****** */

extern
fun topenv_initset_container_source
  {c:cls | c <= GtkContainer} {l:agz} (x: gobjref (c, l)): void
  = "atsui_topenv_initset_container_source"
// end of [topenv_initset_container_source]
extern
fun topenv_initset_textview_source (x: GtkTextView_ref1): void
  = "atsui_topenv_initset_textview_source"
// end of [topenv_initset_textview_source]

//

extern
fun topenv_initset_container_output
  {c:cls | c <= GtkContainer} {l:agz} (x: gobjref (c, l)): void
  = "atsui_topenv_initset_container_output"
// end of [topenv_initset_container_output]
extern
fun topenv_initset_textview_output (x: GtkTextView_ref1): void
  = "atsui_topenv_initset_textview_output"
// end of [topenv_initset_textview_output]

//

extern
fun topenv_initset_statusbar (x: GtkStatusbar_ref1): void
  = "atsui_topenv_initset_statusbar"
// end of [topenv_initset_statusbar]

(* ****** ****** *)

macdef GNULL = (gpointer)null

(* ****** ****** *)

implement
topenv_container_source_set_label
  (name) = () where {
  val (fpf_frm | frm) = topenv_get_container_source ()
  val () = gtk_frame_set_label (frm, name)
  prval () = fpf_frm (frm)
} // end of [topenv_container_source_set_label]

implement
topenv_container_source_update_label () = () where {
  val (fpf_srcwin | srcwin) = $SWL.the_srcwinlst_get_current ()
  val p_srcwin = $SWL.ptr_of_srcwin (srcwin)
  val () =
if p_srcwin > null then let
  val (fpf_name | name) = $SWL.srcwin_get_name (srcwin)
  val (fpf_base | base) = $UT.filename_get_basename (name)
  val (fpf_frm | frm) = topenv_get_container_source ()
  val () = gtk_frame_set_label (frm, base)
  prval () = fpf_frm (frm)
  prval () = minus_addback (fpf_base, base | name)
  prval () = minus_addback (fpf_name, name | srcwin)
in
  // nothing
end (* end of [if] *)
  prval () = fpf_srcwin (srcwin)
} // end of [topenv_container_source_set_label]

(* ****** ****** *)

// "Comic sans MS 10"
#define TEXTVIEW_FONT "Courier 12" // a font of fixed-size

extern
fun topenv_make_textview_source (): GtkTextView_ref1
implement
topenv_make_textview_source () = let
  val tb = gtk_text_buffer_new_null ()
  val tv = gtk_text_view_new_with_buffer (tb)
  val () = g_object_unref (tb)
  // val () = gtk_widget_grab_focus (tv) // HX: what does this mean?
//
  val (fpf_name | name) = __cast (TEXTVIEW_FONT) where {
    extern castfn __cast (x: string): [l:agz] (gstring l -<lin,prf> void | gstring l)
  } // end of [val]
  val fd = pango_font_description_from_string (name)
//
  val pfd = ptr_of (fd)
  val () = (print "pfd = "; print pfd; print_newline ())
  val () = gtk_widget_modify_font (tv, fd)
//
  val () = pango_font_description_free (fd)
  prval () = fpf_name (name)
  val () = gtk_text_view_set_editable (tv, GFALSE)
  val () = gtk_text_view_set_cursor_visible (tv, GFALSE)
in
  tv (* return *)
end // end of [topenv_make_textview_source]

(* ****** ****** *)

extern
fun topenv_make_textview_output (): GtkTextView_ref1
implement
topenv_make_textview_output () = let
  val tb = gtk_text_buffer_new_null ()
  val [l_tv:addr] tv = gtk_text_view_new_with_buffer (tb)
  val () = gtk_text_view_set_editable (tv, GFALSE)
  val () = gtk_text_view_set_cursor_visible (tv, GFALSE)
//
  val (fpf_x | x) = (gs)"(No compilation output yet)"  
  val () = gtk_text_buffer_setall_text (tb, x)
  prval () = fpf_x (x)
//
  val () = g_object_unref (tb)
in
  tv (* return *)
end // end of [topenv_make_textview_output]

(* ****** ****** *)

implement topenv_textview_source_initset_if () = let
  val tvflag = topenv_textview_source_initset_flag_get ()
in
  if tvflag = 0 then let
    val win = gtk_scrolled_window_new_null ()
    val () = gtk_scrolled_window_set_policy
      (win, GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC)
    val tv = topenv_make_textview_source ()
    val () = gtk_container_add (win, tv)
    val () = gtk_widget_show (tv)
    val () = topenv_initset_textview_source (tv)
//
    val (fpf_x | x) = topenv_get_menuitem_file_close ()
    val () = gtk_widget_set_sensitive (x, GTRUE)
    prval () = fpf_x (x)
    val (fpf_x | x) = topenv_get_menuitem_file_save ()
    val () = gtk_widget_set_sensitive (x, GTRUE)
    prval () = fpf_x (x)
    val (fpf_x | x) = topenv_get_menuitem_file_saveas ()
    val () = gtk_widget_set_sensitive (x, GTRUE)
    prval () = fpf_x (x)
//
    val () = the_drawarea_welcome_fini ()
    val (fpf_container | container) = topenv_get_container_source ()
    val () = gtk_container_add (container, win)
    val () = gtk_widget_show_unref (win)
    prval () = fpf_container (container)
  in
    // nothing
  end // end of [val]
end // end of [topenv_textview_source_initset_if]

(* ****** ****** *)

extern
fun topenv_make_menu_edit (): GtkMenu_ref1
implement
topenv_make_menu_edit () = menu where {
  val menu = gtk_menu_new () // to be returned
//
  val undo_item =
    $UT.gtk_image_menu_item_new_from_stock_null (GTK_STOCK_UNDO)
  val () = gtk_menu_shell_append (menu, undo_item)
  val () = gtk_widget_show_unref (undo_item)
//
  val redo_item =
    $UT.gtk_image_menu_item_new_from_stock_null (GTK_STOCK_REDO)
  val () = gtk_menu_shell_append (menu, redo_item)
  val () = gtk_widget_show_unref (redo_item)
//
  val sep_item = gtk_separator_menu_item_new ()
  val () = gtk_menu_shell_append (menu, sep_item)
  val () = gtk_widget_show_unref (sep_item)
//
  val paste_item =
    $UT.gtk_image_menu_item_new_from_stock_null (GTK_STOCK_PASTE)
  val () = gtk_menu_shell_append (menu, paste_item)
  val () = gtk_widget_show_unref (paste_item)
//
  val sep_item = gtk_separator_menu_item_new ()
  val () = gtk_menu_shell_append (menu, sep_item)
  val () = gtk_widget_show_unref (sep_item)
//
  val delete_item =
    $UT.gtk_image_menu_item_new_from_stock_null (GTK_STOCK_DELETE)
  val () = gtk_menu_shell_append (menu, delete_item)
  val () = gtk_widget_show_unref (delete_item)
//
} // end of [EDITmenu_make]

(* ****** ****** *)

fn toggle_statusbar
  (tf: gboolean) = () where {
  val tf = (bool_of)tf
  val (fpf_bar | bar) = topenv_get_statusbar ()
  val () = (
    if tf then gtk_widget_show (bar) else gtk_widget_hide (bar)
  ) : void
  prval () = fpf_bar (bar)
} // end of [cb_toggle_statusbar]

fun cb_view_statusbar {l:agz}
  (item: !GtkCheckMenuItem_ref l)
  : gboolean = GTRUE where {
  val active = gtk_check_menu_item_get_active (item)
  val () = toggle_statusbar (active)
} // end of [cb_view_statusbar]

extern
fun topenv_make_menu_view (): GtkMenu_ref1
implement
topenv_make_menu_view () = menu where {
  val menu = gtk_menu_new () // to be returned
//
  val (fpf_x | x) = (gs)"View Statusbar"
  val statusbar_item = gtk_check_menu_item_new_with_label (x)
  val () = gtk_check_menu_item_set_active (statusbar_item, GFALSE)
  prval () = fpf_x (x)
//
  val _sid = g_signal_connect
    (statusbar_item, (gsignal)"activate", G_CALLBACK(cb_view_statusbar), GNULL)
//
  val () = gtk_menu_shell_append (menu, statusbar_item)
  val () = gtk_widget_show_unref (statusbar_item)
} // end of [topenv_make_menu_view]

(* ****** ****** *)

extern
fun theMenubar_make (): GtkMenuBar_ref1
implement
theMenubar_make () = mbar where {
  val [l_bar:addr] mbar = gtk_menu_bar_new ()
//
  val () = () where { // adding the FILE menu
    val item = $UT.gtk_menu_item_new_with_mnemonic ("_File")
    val menu = topenv_make_menu_file ()
    val () = gtk_menu_item_set_submenu (item, menu)
    val () = initset (menu) where {
      extern fun initset (x: GtkMenu_ref1): void = "atsui_topenv_initset_menu_file"
    } // end of [val]
    val () = gtk_menu_shell_append (mbar, item)
    val () = gtk_widget_show_unref (item)
  } // end of [val]
//
  val () = () where { // adding the EDIT menu
    val item = $UT.gtk_menu_item_new_with_mnemonic ("_Edit")
    val menu = topenv_make_menu_edit ()
    val () = gtk_menu_item_set_submenu (item, menu)
    val () = g_object_unref (menu)
    val () = gtk_menu_shell_append (mbar, item)
    val () = gtk_widget_show_unref (item)
  } // end of [val]
//
  val () = () where { // adding the VIEW menu
    val item = $UT.gtk_menu_item_new_with_mnemonic ("_View")
    val menu = topenv_make_menu_view ()
    val () = gtk_menu_item_set_submenu (item, menu)
    val () = g_object_unref (menu)
    val () = gtk_menu_shell_append (mbar, item)
    val () = gtk_widget_show_unref (item)
  } // end of [val]
//
  val () = () where { // adding the WINDOW menu
    val item = $UT.gtk_menu_item_new_with_mnemonic ("_Window")
    val [l:addr] menu = topenv_make_menu_window ()
//
    val f = lam (
        menu: !gobjref (GtkMenuShell, l)
      ): gboolean => GFALSE where {
      val (fpf_x | x) = $SWL.the_srcwinlst_get_current ()
      val px = $SWL.ptr_of_srcwin (x)
      val () = if px > null then let
        val (fpf_itm | itm) = $SWL.srcwin_get_menuitm (x)
        val () = gtk_menu_shell_select_item (menu, itm)
        prval () = minus_addback (fpf_itm, itm | x)
      in
        // nothing
      end // end of [val]
      prval () = fpf_x (x)
    } // end of [val]
//
    val _sid = g_signal_connect_swapped
      (item, (gsignal)"activate", G_CALLBACK(f), menu)
    val () = gtk_menu_item_set_submenu (item, menu)
    val () = initset (menu) where {
      extern fun initset (x: GtkMenu_ref1): void = "atsui_topenv_initset_menu_window"
    } // end of [val]
    val () = gtk_menu_shell_append (mbar, item)
    val () = gtk_widget_show_unref (item)
  } // end of [val]
} // end of [theMenubar_make]

(* ****** ****** *)

fun the_drawarea_welcome_cairodraw {l:agz} 
  (cr: !cairo_ref l, width: int, height: int): void = () where {
//
  #define FONTSIZE 1
  val () = cairo_select_font_face
    (cr, "Georgia", CAIRO_FONT_SLANT_ITALIC, CAIRO_FONT_WEIGHT_BOLD)
  val () = cairo_set_font_size (cr, (double_of)FONTSIZE)
//
  val W = (double_of)width and H = (double_of)height
  val () = () where {
    val utf8 = "ATS: Unleashing the potential of types!"
    var te : cairo_text_extents_t
//
    val () = cairo_text_extents (cr, utf8, te)
    val alpha = (1.0 * W / te.width) // this is just an estimate
    val () = cairo_translate (cr, W/2, 2*H/5)
    val () = cairo_scale (cr, alpha, alpha)
//
    val () = cairo_text_extents (cr, utf8, te)
    val w = te.width and h = te.height
    val x_base = w / 2 + te.x_bearing and y_base = ~te.y_bearing / 2
    val () = cairo_move_to (cr, ~x_base, y_base)
    val () = cairo_set_source_rgb (cr, 0.25, 0.25, 0.25) // dark gray
    val () = cairo_show_text (cr, utf8)
  } // end of [val]
//
// val () = (print "the_drawarea_welcome_cairodraw: Welcome!"; print_newline ())
//
} // end of [the_drawarea_welcom_cairodraw]

fun the_drawarea_welcome_draw
  {c:cls | c <= GtkDrawingArea} {l:agz}
  (darea: !gobjref (c, l)): void = let
//
  prval () = clstrans {c,GtkDrawingArea,GtkWidget} ()
//
  val (fpf_win | win) = gtk_widget_get_window (darea)
in
  if g_object_isnot_null (win) then let
    val cr = gdk_cairo_create (win)
    prval () = minus_addback (fpf_win, win | darea)
    val (pf, fpf | p) = gtk_widget_getref_allocation (darea)
    val () = the_drawarea_welcome_cairodraw (cr, (int_of)p->width, (int_of)p->height)
    prval () = minus_addback (fpf, pf | darea)
    val () = cairo_destroy (cr)
  in
    // nothing
  end else let
    prval () = minus_addback (fpf_win, win | darea)
  in
    // nothing
  end (* end of [if] *)
end // end of [the_drawarea_welcome_draw]

fun the_drawarea_welcome_expose
  (): gboolean = GFALSE where {
  val darea = the_drawarea_welcome_get ()
  val () = the_drawarea_welcome_draw (darea)
  val () = the_drawarea_welcome_set (darea)
} // end of [the_drawarea_welcom_expose]

(* ****** ****** *)

extern
fun theFunctionlst_make (): GtkAlignment_ref1
implement
theFunctionlst_make () = let
  val valign = gtk_alignment_new (0.5f, 0.0f, 0.0f, 0.0f)
  val vbox = gtk_vbox_new (GFALSE(*home*), gint(0)(*spacing*))
  val () = gtk_container_add (valign, vbox)
//
  val btn_compile = $UT.gtk_button_new_with_label ("Compile")
  val _sid = g_signal_connect (
    btn_compile, (gsignal)"clicked", G_CALLBACK(cb_compile_clicked_if), GNULL
  ) // end of [g_signal_connect]
  val () = gtk_box_pack_start (vbox, btn_compile, GFALSE, GFALSE, (guint)2)
  val () = gtk_widget_show_unref (btn_compile)
//
  val () = gtk_widget_show_unref (vbox)
//
in
  valign
end // end of [theFunctionlst_make]

(* ****** ****** *)

extern 
fun theHPaned1_make (): GtkHPaned_ref1
implement theHPaned1_make () = hpaned0 where {
//
  val hpaned0 = gtk_hpaned_new ()
//
  // HX: leave it empty for now
  val win1 = gtk_text_view_new ()
  val () = gtk_paned_add1 (hpaned0, win1)
  // val () = gtk_widget_show (win1) // HX: default: hidden
  val () = g_object_unref (win1)
//
  val vpaned2 = gtk_vpaned_new ()
  val () = gtk_paned_add2 (hpaned0, vpaned2)
//
  #define NROW 24
  #define NCOL 48
  val table2 = gtk_table_new
    ((guint)NROW, (guint)NCOL, GFALSE(*homo*))
  val () = gtk_paned_pack1 (vpaned2, table2, GTRUE(*resize*), GTRUE(*shrink*))
  val top2 = 0U and bot2 = uint_of(NROW)
//
  val win21 = $UT.gtk_frame_new ("Welcome")
  val darea = gtk_drawing_area_new ()
  val _sid = g_signal_connect
    (darea, (gsignal)"expose-event", G_CALLBACK (the_drawarea_welcome_expose), GNULL)
  // end of [_sid]
  val () = gtk_container_add (win21, darea)
  val () = gtk_widget_show (darea)
  val () = the_drawarea_welcome_set (darea)
//
  val left21 = 0U
  val right21 = uint_of(23*NCOL/24)
  val xopt = GTK_FILL lor GTK_EXPAND
  and yopt = GTK_FILL lor GTK_EXPAND
  val () = gtk_table_attach (
    table2, win21, left21, right21, top2, bot2, xopt, yopt, 1U, 1U
  ) // end of [val]
  val () = gtk_widget_show (win21)
  val () = topenv_initset_container_source (win21)
//
  val win22 = theFunctionlst_make ()
  val left22 = right21
  val right22 = uint_of(NCOL)
  val () = gtk_table_attach (
    table2, win22, left22, right22, top2, bot2, xopt, yopt, 1U, 1U
  ) // end of [val]
  val () = gtk_widget_show (win22)
  val () = topenv_initset_container_output (win22)
//
  val () = gtk_widget_show_unref (table2)
//
  val win22 = gtk_scrolled_window_new_null ()
  val () = gtk_scrolled_window_set_policy
    (win22, GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC)
  val () = gtk_widget_set_size_request (win22, (gint)0, (gint)72)
  val [l_tv:addr] tv = topenv_make_textview_output ()
  val () = gtk_container_add (win22, tv)
  val () = gtk_widget_show (tv)
  val () = topenv_initset_textview_output (tv)
  val () = gtk_paned_pack2 (vpaned2, win22, GFALSE(*resize*), GFALSE(*shrink*))
  val () = gtk_widget_show_unref (win22)
//
  val () = gtk_widget_show_unref (vpaned2)
//
} // end of [theHPaned_make]

(* ****** ****** *)

extern
fun theStatusbar_make (): GtkStatusbar_ref1
implement theStatusbar_make () = gtk_statusbar_new ()

(* ****** ****** *)

extern
fun theVBox0_make (): GtkVBox_ref1
implement
theVBox0_make () = vbox where {
  val vbox = gtk_vbox_new (GFALSE(*homo*), (gint)0(*spacing*))
//
  val () = () where {
    val mbar = theMenubar_make ()
    val () = gtk_box_pack_start (vbox, mbar, GFALSE, GFALSE, (guint)0)
    val () = gtk_widget_show_unref (mbar)
  } // end of [val]
//
  val () = () where {
    val hpaned = theHPaned1_make ()
    val () = gtk_box_pack_start (vbox, hpaned, GTRUE, GTRUE, (guint)1)
    val () = gtk_widget_show_unref (hpaned)
  } // end of [val]
//
  val () = () where {
    val statusbar = theStatusbar_make ()
    val () = gtk_box_pack_start (vbox, statusbar, GFALSE, GFALSE, (guint)1)
    // val () = gtk_widget_show (statusbar) // HX: default: hidden
    val () = topenv_initset_statusbar (statusbar)
  } // end of [val]
//
} // end of [theVBox0_make]

(* ****** ****** *)

implement
topenv_init () = () where {
  val win = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val _sid = g_signal_connect
    (win, (gsignal)"delete_event", G_CALLBACK(cb_quit_activate), GNULL)
//
  val (fpf_x | x) = (gs)"ATSUI"
  val () = gtk_window_set_title (win, x)
  prval () = fpf_x (x)
//
  val () = gtk_widget_set_size_request (win, (gint)800, (gint)540)
  val () = gtk_window_set_position (win, GTK_WIN_POS_CENTER)
//
  val aclgrp = gtk_accel_group_new ()
  val () = gtk_window_add_accel_group (win, aclgrp)
  val () = topenv_initset_aclgrp (aclgrp)
//
  val vbox = theVBox0_make ()
  val () = gtk_container_add (win, vbox)
  val () = gtk_widget_show (vbox)
  val () = topenv_initset_vbox0 (vbox)
//
// val () = gtk_widget_show (win) // this is to be done in [atsui_main]
//
  val () = topenv_initset_topwin (win)
} // end of [topenv_init]

implement
topenv_fini () = () where {
  val () = gtk_main_quit () // quit the main loop
} // end of [topenv_fini]

(* ****** ****** *)

(* end of [atsui_topenv.dats] *)
