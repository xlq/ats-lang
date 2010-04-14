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
// source: gtk/gtkbox.h
//

#define atsctrb_gtk_box_pack_start gtk_box_pack_start
#define atsctrb_gtk_box_pack_end gtk_box_pack_end

/* ****** ****** */

//
// source: gtk/gtkbutton.h
//
#define atsctrb_gtk_button_new gtk_button_new
#define atsctrb_gtk_button_new_with_label gtk_button_new_with_label
#define atsctrb_gtk_button_new_with_mnemonic gtk_button_new_with_mnemonic

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

#define atsctrb_gtk_hbox_new gtk_hbox_new

/* ****** ****** */

//
// source: gtk/gtkhseparator.h
//

#define atsctrb_gtk_hseparator_new gtk_hseparator_new

/* ****** ****** */

//
// source: gtk/gtklabel.h
//

#define atsctrb_gtk_label_new gtk_label_new

/* ****** ****** */

//
// source: gtk/gtkmisc.h
//

#define atsctrb_gtk_misc_get_alignment gtk_misc_get_alignment
#define atsctrb_gtk_misc_set_alignment gtk_misc_set_alignment

/* ****** ****** */

//
// source: gtk/gtkradiobutton.h
//

#define atsctrb_gtk_radio_button_new_with_label gtk_radio_button_new_with_label
#define atsctrb_gtk_radio_button_new_with_label_from_widget gtk_radio_button_new_with_label_from_widget

#define atsctrb_gtk_radio_button_get_group gtk_radio_button_get_group
#define atsctrb_gtk_radio_button_set_group gtk_radio_button_set_group

/* ****** ****** */

//
// source: gtk/gtkrange.h
//

#define atsctrb_gtk_range_get_adjustment gtk_range_get_adjustment
#define atsctrb_gtk_range_set_adjustment gtk_range_set_adjustment

/* ****** ****** */

//
// source: gtk/gtktable.h
//

#define atsctrb_gtk_table_new gtk_table_new

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

#define atsctrb_gtk_toggle_button_new gtk_toggle_button_new
#define atsctrb_gtk_toggle_button_new_with_label gtk_toggle_button_new_with_label
#define atsctrb_gtk_toggle_button_new_with_mnemonic gtk_toggle_button_new_with_mnemonic

#define atsctrb_gtk_toggle_button_get_active gtk_toggle_button_get_active
#define atsctrb_gtk_toggle_button_set_active gtk_toggle_button_set_active

/* ****** ****** */

//
// source: gtk/gtkvbox.h
//

#define atsctrb_gtk_vbox_new gtk_vbox_new

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
#define atsctrb_gtk_window_new gtk_window_new
#define atsctrb_gtk_window_set_title gtk_window_set_title

/* ****** ****** */

#endif // end of [ATSCTRB_GTK_CATS]
