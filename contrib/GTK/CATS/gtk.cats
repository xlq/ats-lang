/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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
*/

/* ****** ****** */

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: April, 2010

/* ****** ****** */

#ifndef ATSCTRB_GTK_CATS
#define ATSCTRB_GTK_CATS

/* ****** ****** */

#include "gtk/gtk.h"

/* ****** ****** */

//
// source: gtk/gtkmain.h
//
#define atsctrb_gtk_main gtk_main
#define atsctrb_gtk_main_level gtk_main_level
#define atsctrb_gtk_main_quit gtk_main_quit

/* ****** ****** */

//
// source: gtk/gtkarrow.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_arrow_new (
  GtkArrowType arrow_type
, GtkShadowType shadow_type
) {
  GtkWidget *widget = gtk_arrow_new(arrow_type, shadow_type);
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_arrow_new]

#define atsctrb_gtk_arrow_set gtk_arrow_set

/* ****** ****** */

//
// source: gtk/gtkbox.h
//

#define atsctrb_gtk_box_pack_start gtk_box_pack_start
#define atsctrb_gtk_box_pack_end gtk_box_pack_end

/* ****** ****** */

//
// source: gtk/gtkbutton.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_button_new () {
  GtkWidget *widget = gtk_button_new() ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_button_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_button_new_with_label
  (ats_ptr_type label) {
  GtkWidget *widget = gtk_button_new_with_label((gchar*)label) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_button_new_with_label]

ATSinline()
ats_ptr_type
atsctrb_gtk_button_new_with_mnemonic
  (ats_ptr_type label) {
  GtkWidget *widget = gtk_button_new_with_mnemonic((gchar*)label) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_button_new_with_mnemonic]

/* ****** ****** */

//
// source: gtk/gtkcontainer.h
//

#define atsctrb_gtk_container_add gtk_container_add
#define atsctrb_gtk_container_set_border_width gtk_container_set_border_width

/* ****** ****** */

//
// source: gtk/gtkhbox.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_hbox_new (
  gboolean homo, gint spacing
) {
  GtkWidget *widget = gtk_hbox_new (homo, spacing) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_hbox_new]

/* ****** ****** */

//
// source: gtk/gtkhscale.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_hscale_new
  (ats_ptr_type adj) {
  GtkWidget *widget = gtk_hscale_new ((GtkAdjustment*)adj) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_hscale_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_hscale_new_with_range
  (gdouble min, gdouble max, gdouble step) {
  GtkWidget *widget = gtk_hscale_new_with_range (min, max, step) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_hscale_new_with_range]

/* ****** ****** */

//
// source: gtk/gtkhseparator.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_hseparator_new () {
  GtkWidget *widget = gtk_hseparator_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_hseparator_new]

/* ****** ****** */

//
// source: gtk/gtklabel.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_label_new (ats_ptr_type name) {
  GtkWidget *widget = gtk_label_new ((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_label_new]

/* ****** ****** */

//
// Source: gtk/gtkmisc.h
//

#define atsctrb_gtk_misc_get_alignment gtk_misc_get_alignment
#define atsctrb_gtk_misc_set_alignment gtk_misc_set_alignment

/* ****** ****** */

//
// source: gtk/gtkradiobutton.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_radio_button_new
  (ats_ptr_type group) {
  GtkWidget *widget = gtk_radio_button_new ((GSList*)group) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_radio_button_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_radio_button_new_with_label
  (ats_ptr_type group, ats_ptr_type name) {
  GtkWidget *widget =
    gtk_radio_button_new_with_label ((GSList*)group, (gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_radio_button_new_with_label]

ATSinline()
ats_ptr_type
atsctrb_gtk_radio_button_new_with_mnemonic
  (ats_ptr_type group, ats_ptr_type name) {
  GtkWidget *widget =
    gtk_radio_button_new_with_mnemonic ((GSList*)group, (gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_radio_button_new_with_mnemonic]

ATSinline()
ats_ptr_type
atsctrb_gtk_radio_button_new_from_widget
  (ats_ptr_type member) {
  GtkWidget *widget =
    gtk_radio_button_new_from_widget ((GtkRadioButton*)member) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_radio_button_new_from_widget]

ATSinline()
ats_ptr_type
atsctrb_gtk_radio_button_new_with_label_from_widget
  (ats_ptr_type member, ats_ptr_type name) {
  GtkWidget *widget =
    gtk_radio_button_new_with_label_from_widget ((GtkRadioButton*)member, (gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_radio_button_new_with_label_from_widget]

#define atsctrb_gtk_radio_button_get_group gtk_radio_button_get_group
#define atsctrb_gtk_radio_button_set_group gtk_radio_button_set_group

/* ****** ****** */

//
// source: gtk/gtkrange.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_adjustment_new (
  gdouble value
, gdouble lower
, gdouble upper
, gdouble step_inc
, gdouble page_inc
, gdouble page_size
) {
  GtkObject *adj = gtk_adjustment_new
    (value, lower, upper, step_inc, page_inc, page_size) ;
  g_object_ref_sink(G_OBJECT(adj)) ; // removing floating reference!
  return adj ;
} // end of [atsctrb_gtk_adjustment_new]

#define atsctrb_gtk_range_get_adjustment gtk_range_get_adjustment
#define atsctrb_gtk_range_set_adjustment gtk_range_set_adjustment

#define atsctrb_gtk_range_set_update_policy gtk_range_set_update_policy

/* ****** ****** */

//
// source: gtk/gtkscale.h
//

#define atsctrb_gtk_scale_set_digits gtk_scale_set_digits
#define atsctrb_gtk_scale_set_value_pos gtk_scale_set_value_pos
#define atsctrb_gtk_scale_set_draw_value gtk_scale_set_draw_value

/* ****** ****** */

//
// source: gtk/gtktable.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_table_new (
  guint rows, guint cols, gboolean homo
) {
  GtkWidget *widget = gtk_table_new (rows, cols, homo) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_table_new]


#define atsctrb_gtk_table_attach gtk_table_attach
#define atsctrb_gtk_table_attach_defaults gtk_table_attach_defaults

#define atsctrb_gtk_table_resize gtk_table_resize

#define atsctrb_gtk_table_set_row_spacing gtk_table_set_row_spacing
#define atsctrb_gtk_table_set_col_spacing gtk_table_set_col_spacing
#define atsctrb_gtk_table_set_row_spacings gtk_table_set_row_spacings
#define atsctrb_gtk_table_set_col_spacings gtk_table_set_col_spacings

/* ****** ****** */

//
// source: gtk/gtktogglebutton.h
//

ats_ptr_type
atsctrb_gtk_toggle_button_new () {
  GtkWidget *widget = gtk_toggle_button_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_toggle_button_new]

ats_ptr_type
atsctrb_gtk_toggle_button_new_with_label
  (ats_ptr_type name) {
  GtkWidget *widget = gtk_toggle_button_new_with_label ((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_toggle_button_new_with_label]

ats_ptr_type
atsctrb_gtk_toggle_button_new_with_mnemonic
  (ats_ptr_type name) {
  GtkWidget *widget = gtk_toggle_button_new_with_mnemonic ((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_toggle_button_new_with_mnemonic]

#define atsctrb_gtk_toggle_button_get_active gtk_toggle_button_get_active
#define atsctrb_gtk_toggle_button_set_active gtk_toggle_button_set_active

/* ****** ****** */

//
// source: gtk/gtkvbox.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_vbox_new (
  gboolean homo, gint spacing
) {
  GtkWidget *widget = gtk_vbox_new (homo, spacing) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_vbox_new]

/* ****** ****** */

//
// source: gtk/gtkvscale.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_vscale_new
  (ats_ptr_type adj) {
  GtkWidget *widget = gtk_vscale_new ((GtkAdjustment*)adj) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_vscale_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_vscale_new_with_range
  (gdouble min, gdouble max, gdouble step) {
  GtkWidget *widget = gtk_vscale_new_with_range (min, max, step) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_vscale_new_with_range]

/* ****** ****** */

//
// source: gtk/gtkvseparator.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_vseparator_new () {
  GtkWidget *widget = gtk_vseparator_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_vseparator_new]

/* ****** ****** */

//
// source: gtk/gtkwidget.h
//

#define atsctrb_GTK_WIDGET_SET_FLAGS GTK_WIDGET_SET_FLAGS

#define atsctrb_gtk_widget_destroy gtk_widget_destroy
#define atsctrb_gtk_widget_show gtk_widget_show
#define atsctrb_gtk_widget_set_size_request gtk_widget_set_size_request
#define atsctrb_gtk_widget_grab_default gtk_widget_grab_default

/* ****** ****** */

//
// source: gtk/gtkwindow.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_window_new
  (GtkWindowType window_type) {
  GtkWidget *widget = gtk_window_new (window_type) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_window_new]

#define atsctrb_gtk_window_set_title gtk_window_set_title

/* ****** ****** */

#endif // end of [ATSCTRB_GTK_CATS]
