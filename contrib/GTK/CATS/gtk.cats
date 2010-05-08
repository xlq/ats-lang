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

ATSinline()
GtkAttachOptions
atsctrb_lor_GtkAttachOptions_GtkAttachOptions
  (GtkAttachOptions x1, GtkAttachOptions x2) { return (x1 | x2) ; }
// end of [atsctrb_lor_GtkAttachOptions_GtkAttachOptions]

ATSinline()
GtkAccelFlags
atsctrb_lor_GtkAccelFlags_GtkAccelFlags
  (GtkAccelFlags x1, GtkAccelFlags x2) { return (x1 | x2) ; }
// end of [atsctrb_lor_GtkAccelFlags_GtkAccelFlags]

/* ****** ****** */

//
// source: gtk/gtkaccelgroup.h
//

//
// HX-2010-05-02:
// it is a direct subclass of GObject, so there is no floating reference
//
#define atsctrb_gtk_accel_group_new gtk_accel_group_new

/* ****** ****** */

//
// source: gtk/gtkadjustment.h
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

#define atsctrb_gtk_adjustment_get_value gtk_adjustment_get_value
#define atsctrb_gtk_adjustment_set_value gtk_adjustment_set_value

/* ****** ****** */

//
// source: gtk/gtkalignment.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_alignment_new (
  gfloat xalign
, gfloat yalign
, gfloat xscale
, gfloat yscale
) {
  GtkWidget *widget =
    gtk_alignment_new (xalign, yalign, xscale, yscale) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_alignment_new]

#define atsctrb_gtk_alignment_set gtk_alignment_set

#define atsctrb_gtk_alignment_get_padding gtk_alignment_get_padding
#define atsctrb_gtk_alignment_set_padding gtk_alignment_set_padding

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
  (ats_ptr_type name) {
  GtkWidget *widget = gtk_button_new_with_label((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_button_new_with_label]

ATSinline()
ats_ptr_type
atsctrb_gtk_button_new_with_mnemonic
  (ats_ptr_type name) {
  GtkWidget *widget = gtk_button_new_with_mnemonic((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_button_new_with_mnemonic]

ATSinline()
ats_ptr_type
atsctrb_gtk_button_new_from_stock
  (ats_ptr_type stock_id) {
  GtkWidget *widget = gtk_button_new_from_stock((gchar*)stock_id) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_button_new_from_stock]

/* ****** ****** */

ATSinline()
ats_ptr_type
atsctrb_gtk_button_get_label
  (ats_ptr_type button) {
  // HX: a string constant is returned:
  return (void*)gtk_button_get_label((GtkButton*)button) ;
} // end of [atsctrb_gtk_button_get_label]

#define atsctrb_gtk_button_set_label gtk_button_set_label

/* ****** ****** */

//
// source: gtk/gtkcheckbutton.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_check_button_new () {
  GtkWidget *widget = gtk_check_button_new() ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_check_button_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_check_button_new_with_label
  (ats_ptr_type name) {
  GtkWidget *widget = gtk_check_button_new_with_label((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_check_button_new_with_label]

ATSinline()
ats_ptr_type
atsctrb_gtk_check_button_new_with_mnemonic
  (ats_ptr_type name) {
  GtkWidget *widget = gtk_check_button_new_with_mnemonic((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_check_button_new_with_mnemonic]

/* ****** ****** */

//
// source: gtk/gtkcontainer.h
//

#define atsctrb_gtk_container_add gtk_container_add
#define atsctrb_gtk_container_remove gtk_container_remove

#define atsctrb_gtk_container_set_border_width gtk_container_set_border_width

/* ****** ****** */

//
// source: gtk/gtkcolorsel.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_color_selection_new () {
  GtkWidget *widget = gtk_color_selection_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_color_selection_new]

#define atsctrb_gtk_color_selection_get_previous_color \
  gtk_color_selection_get_previous_color
#define atsctrb_gtk_color_selection_set_previous_color \
  gtk_color_selection_set_previous_color

#define atsctrb_gtk_color_selection_get_current_color \
  gtk_color_selection_get_current_color
#define atsctrb_gtk_color_selection_set_current_color \
  gtk_color_selection_set_current_color


#define atsctrb_gtk_color_selection_set_has_palette \
  gtk_color_selection_set_has_palette
#define atsctrb_gtk_color_selection_set_has_opacitiy_control \
  gtk_color_selection_set_has_opacitiy_control

/* ****** ****** */

//
// source: gtk/gtkcolorseldialog.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_color_selection_dialog_new
  (ats_ptr_type title) {
  GtkWidget *widget = gtk_color_selection_dialog_new ((gchar*)title) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_color_selection_dialog_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_color_selection_dialog_get_colorsel
  (ats_ptr_type colorseldlg) {
  return ((GtkColorSelectionDialog*)colorseldlg)->colorsel ;
} // end of [...]

/* ****** ****** */

//
// source: gtk/gtkdialog.h
//

ATSinline()
GtkDialogFlags
atsctrb_lor_GtkDialogFlags_GtkDialogFlags
  (GtkDialogFlags x1, GtkDialogFlags x2) { return (x1 | x2) ; }
// end of [atsctrb_lor_GtkDialogFlags_GtkDialogFlags]

ATSinline()
ats_ptr_type
atsctrb_gtk_dialog_new () {
  GtkWidget *widget = gtk_dialog_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_dialog_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_dialog_get_window
  (ats_ptr_type dialog) {
  return &((GtkDialog*)dialog)->window ;
} // end of [gtk_dialog_get_window]

ATSinline()
ats_ptr_type
atsctrb_gtk_dialog_get_vbox
  (ats_ptr_type dialog) {
  return ((GtkDialog*)dialog)->vbox ;
} // end of [...]

ATSinline()
ats_ptr_type
atsctrb_gtk_dialog_get_action_area
  (ats_ptr_type dialog) {
  return ((GtkDialog*)dialog)->action_area ;
} // end of [...]

#define atsctrb_gtk_dialog_add_button gtk_dialog_add_button

#define atsctrb_gtk_dialog_run gtk_dialog_run

/* ****** ****** */

//
// source: gtk/gtkdrawingarea.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_drawing_area_new () {
  GtkWidget *widget = gtk_drawing_area_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_drawing_area_new]

/* ****** ****** */

//
// source: gtk/gtkentry.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_entry_new () {
  GtkWidget *widget = gtk_entry_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_entry_new]

#define atsctrb_gtk_entry_get_editable gtk_entry_get_editable
#define atsctrb_gtk_entry_set_editable gtk_entry_set_editable

#define atsctrb_gtk_entry_get_visibility gtk_entry_get_visibility
#define atsctrb_gtk_entry_set_visibility gtk_entry_set_visibility

#define atsctrb_gtk_entry_get_max_length gtk_entry_get_max_length
#define atsctrb_gtk_entry_set_max_length gtk_entry_set_max_length

ATSinline()
ats_ptr_type
atsctrb_gtk_entry_get_text
  (ats_ptr_type entry) {
  // it returns a const pointer
  return (void*)gtk_entry_get_text((GtkEntry*)entry) ;
}
#define atsctrb_gtk_entry_set_text gtk_entry_set_text

/* ****** ****** */

//
// source: gtk/gtkfilechooser.h
//

#define atsctrb_GTK_FILE_CHOOSER GTK_FILE_CHOOSER

ATSinline()
ats_ptr_type
atsctrb_gtk_file_chooser_get_filename
  (ats_ptr_type filesel) {
  (void*)gtk_file_chooser_get_filename ((GtkFileChooser*)filesel) ;
} // end of [atsctrb_gtk_file_chooser_get_filename]
#define atsctrb_gtk_file_chooser_set_filename gtk_file_chooser_set_filename

#define atsctrb_gtk_file_chooser_get_do_overwrite_confirmation \
  gtk_file_chooser_get_do_overwrite_confirmation
#define atsctrb_gtk_file_chooser_set_do_overwrite_confirmation \
  gtk_file_chooser_set_do_overwrite_confirmation

/* ****** ****** */

//
// source: gtk/gtkfilechooserdialog.h
//
ATSinline()
ats_ptr_type
atsctrb_gtk_file_chooser_dialog_new (
  ats_ptr_type title, GtkFileChooserAction action
) {
  GtkWidget *widget = gtk_file_chooser_dialog_new (
    (gchar*)title
  , NULL // parent window
  , action
  , NULL // button/reponse_id pairs
  ) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_file_chooser_dialog_new]

/* ****** ****** */

//
// source: gtk/gtkfilesel.h
//
// HX-2010-04-19:
// this is all DEPRECATED; please use gtk/gtkfilechooserdialog.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_file_selection_new
  (ats_ptr_type title) {
  GtkWidget *widget = gtk_file_selection_new ((gchar*)title) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_file_selection_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_file_selection_get_ok_button
  (ats_ptr_type filesel) {
  return ((GtkFileSelection*)filesel)->ok_button ;
} // end of [...]

ATSinline()
ats_ptr_type
atsctrb_gtk_file_selection_get_cancel_button
  (ats_ptr_type filesel) {
  return ((GtkFileSelection*)filesel)->cancel_button ;
} // end of [...]

ATSinline()
ats_ptr_type
atsctrb_gtk_file_selection_get_filename
  (ats_ptr_type filesel) {
  (void*)gtk_file_selection_get_filename ((GtkFileSelection*)filesel) ;
} // end of [atsctrb_gtk_file_selection_get_filename]

#define atsctrb_gtk_file_selection_set_filename gtk_file_selection_set_filename

/* ****** ****** */

//
// source: gtk/gtkframe.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_frame_new (ats_ptr_type name) {
  GtkWidget *widget = gtk_frame_new ((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_frame_new]

#define atsctrb_gtk_frame_new_null() atsctrb_gtk_frame_new(NULL)

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
// source: gtk/gtkhruler.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_hruler_new () {
  GtkWidget *widget = gtk_hruler_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_hruler_new]

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
// source: gtk/gtkhsrollbar.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_hscrollbar_new
  (ats_ptr_type adj) {
  GtkWidget *widget = gtk_hscrollbar_new ((GtkAdjustment*)adj) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_hscrollbar_new]

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
// source: gtk/gtkimagemenuitem.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_image_menu_item_new () {
  GtkWidget *widget = gtk_image_menu_item_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_image_menu_item_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_image_menu_item_new_with_label
  (ats_ptr_type name) {
  GtkWidget *widget = gtk_image_menu_item_new_with_label ((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_image_menu_item_new_with_label]

ATSinline()
ats_ptr_type
atsctrb_gtk_image_menu_item_new_with_mnemonic
  (ats_ptr_type name) {
  GtkWidget *widget = gtk_image_menu_item_new_with_mnemonic ((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_image_menu_item_new_with_mnemonic]

ATSinline()
ats_ptr_type
atsctrb_gtk_image_menu_item_new_from_stock
  (ats_ptr_type name, ats_ptr_type aclgrp) {
  GtkWidget *widget =
    gtk_image_menu_item_new_from_stock ((gchar*)name, (GtkAccelGroup*)aclgrp) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_image_menu_item_new_from_stock]

#define atsctrb_gtk_image_menu_item_new_from_stock_null(name) \
  atsctrb_gtk_image_menu_item_new_from_stock(name, NULL)

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

#define atsctrb_gtk_label_get_text gtk_label_get_text
#define atsctrb_gtk_label_set_text gtk_label_set_text

#define atsctrb_gtk_label_get_justify gtk_label_get_justify
#define atsctrb_gtk_label_set_justify gtk_label_set_justify

#define atsctrb_gtk_label_get_line_wrap gtk_label_get_line_wrap
#define atsctrb_gtk_label_set_line_wrap gtk_label_set_line_wrap

/* ****** ****** */

//
// source: gtk/gtkmenu.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_menu_new () {
  GtkWidget *widget = gtk_menu_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_menu_new]

#define atsctrb_gtk_menu_popup_null(menu, button, time) \
  gtk_menu_popup(menu, NULL, NULL, NULL, NULL, button, time)

/* ****** ****** */

//
// source: gtk/gtkmenubar.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_menu_bar_new () {
  GtkWidget *widget = gtk_menu_bar_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_menu_bar_new]

/* ****** ****** */

//
// source: gtk/gtkmenuitem.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_menu_item_new () {
  GtkWidget *widget = gtk_menu_item_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_menu_item_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_menu_item_new_with_label
  (ats_ptr_type name) {
  GtkWidget *widget = gtk_menu_item_new_with_label ((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_menu_item_new_with_label]

ATSinline()
ats_ptr_type
atsctrb_gtk_menu_item_new_with_mnemonic (ats_ptr_type name) {
  GtkWidget *widget = gtk_menu_item_new_with_mnemonic ((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_menu_item_new_with_mnemonic]

#if GTK_CHECK_VERSION(2, 16, 0)
// >= GTK-2.16
#define atsctrb_gtk_menu_item_get_label gtk_menu_item_get_label
// >= GTK-2.16
#define atsctrb_gtk_menu_item_set_label gtk_menu_item_set_label
#else
//
// HX-2010-05-06: a kludge that can be scratched at any moment
//
ATSinline()
ats_ptr_type
atsctrb_gtk_menu_item_get_label (
  ats_ptr_type menu_item, ats_ptr_type label
) {
  if (GTK_IS_LABEL (GTK_BIN (menu_item)->child))
    return (void*)gtk_label_get_label (GTK_LABEL (GTK_BIN (menu_item)->child)) ;
  return NULL ;
} // end of [atsctrb_gtk_menu_item_let_label]
//
ATSinline()
ats_void_type
atsctrb_gtk_menu_item_set_label (
  ats_ptr_type menu_item, ats_ptr_type label
) {
  if (GTK_IS_LABEL (GTK_BIN (menu_item)->child)) {
    gtk_label_set_label
      (GTK_LABEL (GTK_BIN (menu_item)->child), label ? (gchar*)label : (gchar*)"") ;
    // g_object_notify (G_OBJECT (menu_item), "label"); // not really available
  } ;
  return ;
} // end of [atsctrb_gtk_menu_item_set_label]
//
#endif // GTK_CHECK_VERSION(2, 16, 0)

#define atsctrb_gtk_menu_item_set_submenu gtk_menu_item_set_submenu

/* ****** ****** */

//
// source: gtk/gtkmenushell.h
//

#define atsctrb_gtk_menu_shell_append gtk_menu_shell_append
#define atsctrb_gtk_menu_shell_prepend gtk_menu_shell_prepend

#define atsctrb_gtk_menu_shell_select_item gtk_menu_shell_select_item
#define atsctrb_gtk_menu_shell_select_first gtk_menu_shell_select_first

#define atsctrb_gtk_menu_shell_deselect gtk_menu_shell_deselect

/* ****** ****** */

//
// source: gtk/gtkmessagedialog.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_message_dialog_new0 (
  GtkDialogFlags flags
, GtkMessageType type, GtkButtonsType buttons
, ats_ptr_type message
) {
  GtkWidget *widget =
    gtk_message_dialog_new (NULL, flags, type, buttons, (gchar*)message) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_message_dialog_new0]

ATSinline()
ats_ptr_type
atsctrb_gtk_message_dialog_new0_with_markup (
  GtkDialogFlags flags
, GtkMessageType _type, GtkButtonsType buttons
, ats_ptr_type message
) {
  GtkWidget *widget =
    gtk_message_dialog_new_with_markup (NULL, flags, _type, buttons, (gchar*)message) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_message_dialog_new0_with_markup]

#define atsctrb_gtk_message_dialog_set_markup gtk_message_dialog_set_markup

/* ****** ****** */

//
// Source: gtk/gtkmisc.h
//

#define atsctrb_gtk_misc_get_alignment gtk_misc_get_alignment
#define atsctrb_gtk_misc_set_alignment gtk_misc_set_alignment

/* ****** ****** */

//
// source: gtk/gtkoptionmenu.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_option_menu_new () {
  GtkWidget *widget = gtk_option_menu_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_option_menu_new]

#define atsctrb_gtk_option_menu_set_menu gtk_option_menu_set_menu

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

#define atsctrb_gtk_range_get_adjustment gtk_range_get_adjustment
#define atsctrb_gtk_range_set_adjustment gtk_range_set_adjustment

#define atsctrb_gtk_range_set_update_policy gtk_range_set_update_policy

/* ****** ****** */

//
// source: gtk/gtkruler.h
//

#define atsctrb_gtk_ruler_set_metric gtk_ruler_set_metric
#define atsctrb_gtk_ruler_set_range gtk_ruler_set_range

/* ****** ****** */

//
// source: gtk/gtkscale.h
//

#define atsctrb_gtk_scale_set_digits gtk_scale_set_digits
#define atsctrb_gtk_scale_set_value_pos gtk_scale_set_value_pos
#define atsctrb_gtk_scale_set_draw_value gtk_scale_set_draw_value

/* ****** ****** */

//
// source: gtk/gtkscrolledwindow.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_scrolled_window_new (
  ats_ptr_type hadj, ats_ptr_type vadj
) {
  GtkWidget *widget = gtk_scrolled_window_new
    ((GtkAdjustment*)hadj, (GtkAdjustment*)vadj) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_scrolled_window_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_scrolled_window_new_null
  () { return atsctrb_gtk_scrolled_window_new (NULL, NULL) ; }
// end of [atsctrb_gtk_scrolled_window_new_null]

#define atsctrb_gtk_scrolled_window_get_policy gtk_scrolled_window_get_policy
#define atsctrb_gtk_scrolled_window_set_policy gtk_scrolled_window_set_policy

#define atsctrb_gtk_scrolled_window_get_placement gtk_scrolled_window_get_placement
#define atsctrb_gtk_scrolled_window_set_placement gtk_scrolled_window_set_placement

/* ****** ****** */

//
// source: gtk/gtkseparatormenuitem.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_separator_menu_item_new () {
  GtkWidget *widget = gtk_separator_menu_item_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_separator_menu_item_new]

/* ****** ****** */

//
// source: gtk/gtkspinbutton.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_spin_button_new (
  ats_ptr_type adj, gdouble rate, guint digits
) {
  GtkWidget *widget ;
  widget = gtk_spin_button_new ((GtkAdjustment*)adj, rate, digits) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_spin_button_new]

#define atsctrb_gtk_spin_button_configure gtk_spin_button_configure

#define atsctrb_gtk_spin_button_get_range gtk_spin_button_get_range
#define atsctrb_gtk_spin_button_set_range gtk_spin_button_set_range

#define atsctrb_gtk_spin_button_get_value gtk_spin_button_get_value
#define atsctrb_gtk_spin_button_get_value_as_int gtk_spin_button_get_value_as_int
#define atsctrb_gtk_spin_button_set_value gtk_spin_button_set_value

#define atsctrb_gtk_spin_button_get_digits gtk_spin_button_get_digits
#define atsctrb_gtk_spin_button_set_digits gtk_spin_button_set_digits

#define atsctrb_gtk_spin_button_get_numeric gtk_spin_button_get_numeric
#define atsctrb_gtk_spin_button_set_numeric gtk_spin_button_set_numeric

#define atsctrb_gtk_spin_button_get_wrap gtk_spin_button_get_wrap
#define atsctrb_gtk_spin_button_set_wrap gtk_spin_button_set_wrap

#define atsctrb_gtk_spin_button_get_snap_to_ticks gtk_spin_button_get_snap_to_ticks
#define atsctrb_gtk_spin_button_set_snap_to_ticks gtk_spin_button_set_snap_to_ticks

#define atsctrb_gtk_spin_button_spin gtk_spin_button_spin
#define atsctrb_gtk_spin_button_update gtk_spin_button_update

/* ****** ****** */

//
// source: gtk/gtkstatusbar.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_statusbar_new () {
  GtkWidget *widget = gtk_statusbar_new();
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_statusbar_new]

#define atsctrb_gtk_statusbar_push gtk_statusbar_push
#define atsctrb_gtk_statusbar_pop gtk_statusbar_pop
#define atsctrb_gtk_statusbar_remove gtk_statusbar_remove

#define atsctrb_gtk_statusbar_get_context_id gtk_statusbar_get_context_id

#define atsctrb_gtk_statusbar_get_has_resize_grip gtk_statusbar_get_has_resize_grip
#define atsctrb_gtk_statusbar_set_has_resize_grip gtk_statusbar_set_has_resize_grip

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
// source: gtk/gtktextbuffer.h
//

//
// HX-2010-05-03: there is no floating reference involved
//
#define atsctrb_gtk_text_buffer_new_null() gtk_text_buffer_new(NULL)

#define atsctrb_gtk_text_buffer_insert gtk_text_buffer_insert

ATSinline()
ats_void_type
atsctrb_gtk_text_buffer_insertall (
  ats_ptr_type tb, ats_ref_type iter, ats_ptr_type text
) {
  gtk_text_buffer_insert (
    (GtkTextBuffer*)tb, (GtkTextIter*)iter, (gchar*)text, -1
  ) ; return ;
} // end of [atsctrb_gtk_text_buffer_insertall]

//

#define atsctrb_gtk_text_buffer_get_text gtk_text_buffer_get_text
#define atsctrb_gtk_text_buffer_set_text gtk_text_buffer_set_text

ATSinline()
ats_void_type
atsctrb_gtk_text_buffer_setall_text
  (ats_ptr_type tb, ats_ptr_type text) {
  gtk_text_buffer_set_text ((GtkTextBuffer*)tb, (gchar*)text, -1) ;
  return ;
} // end of [atsctrb_gtk_text_buffer_setall_text]

//

#define atsctrb_gtk_text_buffer_get_iter_at_offset \
  gtk_text_buffer_get_iter_at_offset

#define atsctrb_gtk_text_buffer_delete gtk_text_buffer_delete

#define atsctrb_gtk_text_buffer_get_start_iter gtk_text_buffer_get_start_iter
#define atsctrb_gtk_text_buffer_get_end_iter gtk_text_buffer_get_end_iter
#define atsctrb_gtk_text_buffer_get_bounds gtk_text_buffer_get_bounds

#define atsctrb_gtk_text_buffer_place_cursor gtk_text_buffer_place_cursor

/* ****** ****** */

//
// source: gtk/gtktextview.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_text_view_new () {
  GtkWidget *widget = gtk_text_view_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_text_view_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_text_view_new_with_buffer
  (ats_ptr_type tb) {
  GtkWidget *widget =
    gtk_text_view_new_with_buffer ((GtkTextBuffer*)tb) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_text_view_new_with_buffer]

#define atsctrb_gtk_text_view_get_buffer gtk_text_view_get_buffer
#define atsctrb_gtk_text_view_set_buffer gtk_text_view_set_buffer

#define atsctrb_gtk_text_view_get_editable gtk_text_view_get_editable
#define atsctrb_gtk_text_view_set_editable gtk_text_view_set_editable

#define atsctrb_gtk_text_view_get_cursor_visible gtk_text_view_get_cursor_visible
#define atsctrb_gtk_text_view_set_cursor_visible gtk_text_view_set_cursor_visible

#define atsctrb_gtk_text_view_get_window gtk_text_view_get_window

/* ****** ****** */

//
// source: gtk/gtktogglebutton.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_toggle_button_new () {
  GtkWidget *widget = gtk_toggle_button_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_toggle_button_new]

ATSinline()
ats_ptr_type
atsctrb_gtk_toggle_button_new_with_label
  (ats_ptr_type name) {
  GtkWidget *widget = gtk_toggle_button_new_with_label ((gchar*)name) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [gtk_toggle_button_new_with_label]

ATSinline()
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
// source: gtk/gtkvruler.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_vruler_new () {
  GtkWidget *widget = gtk_vruler_new () ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_vruler_new]

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
// source: gtk/gtkvsrollbar.h
//

ATSinline()
ats_ptr_type
atsctrb_gtk_vscrollbar_new
  (ats_ptr_type adj) {
  GtkWidget *widget = gtk_vscrollbar_new ((GtkAdjustment*)adj) ;
  g_object_ref_sink(G_OBJECT(widget)) ; // removing floating reference!
  return widget ;
} // end of [atsctrb_gtk_vscrollbar_new]

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

#define atsctrb_gtk_widget_map gtk_widget_map
#define atsctrb_gtk_widget_unmap gtk_widget_unmap

#define atsctrb_gtk_widget_realize gtk_widget_realize
#define atsctrb_gtk_widget_unrealize gtk_widget_unrealize

#define atsctrb_gtk_widget_show gtk_widget_show
#define atsctrb_gtk_widget_show_now gtk_widget_show_now
#define atsctrb_gtk_widget_show_all gtk_widget_show_all

#define atsctrb_gtk_widget_hide gtk_widget_hide

//
// HX: get out of a GDK window
//
ATSinline()
ats_ptr_type
atsctrb_gtk_widget_get_window
  (ats_ptr_type widget) { return (GTK_WIDGET(widget))->window ; }
// end of [atsctrb_gtk_widget_get_window]

ATSinline()
ats_ptr_type
atsctrb_gtk_widget_getref_allocation
  (ats_ptr_type widget) { return &(GTK_WIDGET(widget))->allocation ; }
// end of [atsctrb_gtk_widget_get_allocation]
#define atsctrb_gtk_widget_get_allocation gtk_widget_get_allocation
#define atsctrb_gtk_widget_set_allocation gtk_widget_set_allocation

#define atsctrb_gtk_widget_set_size_request gtk_widget_set_size_request

#define atsctrb_gtk_widget_grab_default gtk_widget_grab_default

#define atsctrb_gtk_widget_set_events gtk_widget_set_events

#define atsctrb_gtk_widget_add_accelerator gtk_widget_add_accelerator
#define atsctrb_gtk_widget_remove_accelerator gtk_widget_remove_accelerator

#define atsctrb_gtk_widget_modify_fg gtk_widget_modify_fg
#define atsctrb_gtk_widget_modify_bg gtk_widget_modify_bg

#define atsctrb_gtk_widget_get_colormap gtk_widget_get_colormap
#define atsctrb_gtk_widget_modify_font gtk_widget_modify_font

#define atsctrb_gtk_widget_queue_draw_area gtk_widget_queue_draw_area

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
#define atsctrb_gtk_window_set_position gtk_window_set_position
#define atsctrb_gtk_window_set_transient_for gtk_window_set_transient_for

#define atsctrb_gtk_window_get_size gtk_window_get_size
#define atsctrb_gtk_window_set_default_size gtk_window_set_default_size

#define atsctrb_gtk_window_get_resizable gtk_window_get_resizable
#define atsctrb_gtk_window_set_resizable gtk_window_set_resizable

#define atsctrb_gtk_window_add_accel_group gtk_window_add_accel_group
#define atsctrb_gtk_window_remove_accel_group gtk_window_remove_accel_group

/* ****** ****** */

//
// source: gtk/gtkmain.h
//
#define atsctrb_gtk_main gtk_main
#define atsctrb_gtk_main_level gtk_main_level
#define atsctrb_gtk_main_quit gtk_main_quit

#define atsctrb_gtk_timeout_add gtk_timeout_add

/* ****** ****** */

#endif // end of [ATSCTRB_GTK_CATS]

/* end of [gtk.cats] */
