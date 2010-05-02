(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: April, 2010
//

(* ****** ****** *)

%{#
#include "contrib/GTK/CATS/gtk.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staload at run-time

(* ****** ****** *)

staload GLIB = "contrib/glib/SATS/glib.sats"
stadef gboolean = $GLIB.gboolean
//
stadef gchar = $GLIB.gchar
//
stadef gint (i:int) = $GLIB.gint (i)
stadef gint = $GLIB.gint
//
stadef guint (i:int) = $GLIB.guint (i)
stadef guint = $GLIB.guint
//
stadef gfloat = $GLIB.gfloat
stadef gdouble = $GLIB.gdouble
//
stadef gpointer = $GLIB.gpointer
//
stadef gstring = $GLIB.gstring
stadef gstring0 = $GLIB.gstring0
stadef gstring1 = $GLIB.gstring1
//
stadef GSList_ptr = $GLIB.GSList_ptr
stadef GSList_ptr0 = $GLIB.GSList_ptr0
stadef GSList_ptr1 = $GLIB.GSList_ptr1
//
(* ****** ****** *)

staload GOBJ = "contrib/glib/SATS/glib-object.sats"

stadef gobjptr = $GOBJ.gobjptr

stadef GObject = $GOBJ.GObject
stadef GInterface = $GOBJ.GInterface

stadef gsignal = $GOBJ.gsignal

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"

(* ****** ****** *)

//
// class hierarchy for GTK
//
objcls GtkObject = { super: GObject }
  objcls GtkWidget = { super: GtkObject }
    objcls GtkMisc = { super: GtkWidget }
      objcls GtkLabel = { super : GtkMisc }
      objcls GtkArrow = { super : GtkMisc }
      objcls GtkImage = { super : GtkMisc }
      objcls GtkPixmap = { super : GtkMisc }
    // end of [GtkMisc]
    objcls GtkContainer = { super: GtkWidget }
      objcls GtkBin = { super: GtkContainer }
        objcls GtkAlignment = { super: GtkBin }
        objcls GtkFrame = { super: GtkBin }
          objcls GtkAspectFrame = { super: GtkFrame }
        // end of [GtkGrame]
        objcls GtkButton = { super: GtkBin }
          objcls GtkToggleButton = { super: GtkButton }
            objcls GtkCheckButton = { super: GtkToggleButton }
              objcls GtkRadioButton = { super: GtkCheckButton }
            // end of [GtkCheckButton]
          // end of [GtkToggleButton]
          objcls GtkOptionMenu = { super: GtkButton }
        // end of [GtkButton]
        objcls GtkItem = { super: GtkBin }
          objcls GtkMenuItem = { super: GtkItem }
            objcls GtkCheckMenuItem = { super: GtkMenuItem }
              objcls GtkRadioMenuItem = { super: GtkCheckMenuItem }
            // end of [GtkCheckMenuItem]
            objcls GtkImageMenuItem = { super: GtkMenuItem }
            objcls GtkSeparatorMenuItem = { super: GtkMenuItem }
            objcls GtkTearoffMenuItem = { super: GtkMenuItem }
          // end of [GtkMenuItem]
          // objcls GtkListItem = { super: GtkItem } // deprecated since GTK+-2.0
          // objcls GtkTreeItem = { super: GtkItem } // deprecated since GTK+-2.0
        // end of [GtkItem]
        objcls GtkWindow = { super: GtkBin }
          objcls GtkDialog = { super: GtkWindow }
            objcls GtkColorSelectionDialog = { super: GtkDialog }
            objcls GtkFileSelection = { super: GtkDialog } // DEPRECATED!
            objcls GtkFileChooserDialog = { super: GtkDialog }
            objcls GtkFontSelectionDialog = { super: GtkDialog }
            objcls GtkInputDialog = { super: GtkDialog }
            objcls GtkMessageDialog = { super: GtkDialog }
          // end of [GtkDialog]
          objcls GtkPlug = { super: GtkWindow }
        // end of [GtkWindow]
        objcls GtkEventBox = { super: GtkBin }
        objcls GtkHandleBox = { super: GtkBin }
        objcls GtkScrollWindow = { super: GtkBin }
        objcls GtkViewport = { super: GtkBin }
      // end of [GtkBin]
      objcls GtkBox = { super: GtkContainer }
        objcls GtkBottonBox = { super: GtkBox }
          objcls GtkBottonHBox = { super: GtkBottonBox }
          objcls GtkBottonVBox = { super: GtkBottonBox }
        // end of [GtkBottonBox]
        objcls GtkVBox = { super: GtkBox }
          objcls GtkColorSelection = { super: GtkVBox }
          objcls GtkFontSelection = { super: GtkVBox }
          objcls GtkGammarCurve = { super: GtkVBox }
        // end of [GtkVBox]
        objcls GtkHBox = { super: GtkBox }
          objcls GtkCombo = { super: GtkHBox }
          objcls GtkStatusbar = { super: GtkHBox }
        // end of [GtkHBox]
      // end of [GtkBox]
      objcls GtkFixed = { super: GtkContainer }
      objcls GtkPaned = { super: GtkContainer }
        objcls GtkHPaned = { super: GtkPaned }
        objcls GtkVPaned = { super: GtkPaned }
      // end of [GtkPaned]
      objcls GtkLayout = { super: GtkContainer }
      objcls GtkMenuShell = { super: GtkContainer }
        objcls GtkMenuBar = { super: GtkMenuShell }
        objcls GtkMenu = { super: GtkMenuShell }
      // end of [GtkMenuShell]
      objcls GtkNotebook = { super: GtkContainer }
      objcls GtkSocket = { super: GtkContainer }
      objcls GtkTable = { super: GtkContainer }
      objcls GtkTextView = { super: GtkContainer }
      objcls GtkToolbar = { super: GtkContainer }
      objcls GtkTreeView = { super: GtkContainer }
    // end of [GtkContainer]
    objcls GtkCalendar = { super: GtkWidget }
    objcls GtkDrawingArea = { super: GtkWidget }
      objcls GtkCurve = { super: GtkDrawingArea }
    // end of [GtkDrawingArea]
    objcls GtkEditable = { super: GtkWidget }
      objcls GtkEntry = { super: GtkEditable }
        objcls GtkSpinButton = { super: GtkEntry }
      // end of [GtkEntry]
    // end of [GtkEditable]
    objcls GtkRuler = { super: GtkWidget }
      objcls GtkHRuler = { super: GtkRuler }
      objcls GtkVRuler = { super: GtkRuler }
    // end of [GtkScale]
    objcls GtkRange = { super: GtkWidget }
      objcls GtkScale = { super: GtkRange }
        objcls GtkHScale = { super: GtkScale }
        objcls GtkVScale = { super: GtkScale }
      // end of [GtkScale]
      objcls GtkScrollbar = { super: GtkRange }
        objcls GtkHScrollbar = { super: GtkScrollbar }
        objcls GtkVScrollbar = { super: GtkScrollbar }
      // end of [GtkScrollbar]
    // end of [GtkRange]
    objcls GtkSeparator = { super: GtkWidget }
      objcls GtkHSeparator = { super: GtkSeparator }
      objcls GtkVSeparator = { super: GtkSeparator }
    // end of [GtkSeparator]
    objcls GtkInvisible = { super: GtkWidget }
    objcls GtkPreview = { super: GtkWidget }
    objcls GtkProgressBar = { super: GtkWidget }
  // end of [GtkWidget]
  objcls GtkAdjustment = { super: GtkObject }
  objcls GtkCellRenderer = { super: GtkObject }
    objcls GtkCellRendererPixbuf = { super: GtkCellRenderer }
    objcls GtkCellRendererText = { super: GtkCellRenderer }
    objcls GtkCellRendererToggle = { super: GtkCellRenderer }
  // end of [GtkCellRenderer]
  objcls GtkItemFactory = { super: GtkObject }
  objcls GtkTooltips = { super: GtkObject }
  objcls GtkTreeViewColumn = { super: GtkObject }
// end of [GtkObject]

(* ****** ****** *)

viewtypedef GtkAdjustment_ptr (l:addr) = gobjptr (GtkAdjustment, l)
viewtypedef GtkAdjustment_ptr0 = [l:agez] GtkAdjustment_ptr l
viewtypedef GtkAdjustment_ptr1 = [l:addr | l > null] GtkAdjustment_ptr l

viewtypedef GtkAlignment_ptr (l:addr) = gobjptr (GtkAlignment, l)
viewtypedef GtkAlignment_ptr0 = [l:agez] GtkAlignment_ptr l
viewtypedef GtkAlignment_ptr1 = [l:addr | l > null] GtkAlignment_ptr l

viewtypedef GtkArrow_ptr (l:addr) = gobjptr (GtkArrow, l)
viewtypedef GtkArrow_ptr0 = [l:agez] GtkArrow_ptr l
viewtypedef GtkArrow_ptr1 = [l:addr | l > null] GtkArrow_ptr l

viewtypedef GtkButton_ptr (l:addr) = gobjptr (GtkButton, l)
viewtypedef GtkButton_ptr0 = [l:agez] GtkButton_ptr l
viewtypedef GtkButton_ptr1 = [l:addr | l > null] GtkButton_ptr l

viewtypedef GtkCheckButton_ptr (l:addr) = gobjptr (GtkCheckButton, l)
viewtypedef GtkCheckButton_ptr0 = [l:agez] GtkCheckButton_ptr l
viewtypedef GtkCheckButton_ptr1 = [l:addr | l > null] GtkCheckButton_ptr l

viewtypedef GtkColorSelection_ptr (l:addr) = gobjptr (GtkColorSelection, l)
viewtypedef GtkColorSelection_ptr0 = [l:agez] GtkColorSelection_ptr l
viewtypedef GtkColorSelection_ptr1 = [l:addr | l > null] GtkColorSelection_ptr l

viewtypedef GtkColorSelectionDialog_ptr (l:addr) = gobjptr (GtkColorSelectionDialog, l)
viewtypedef GtkColorSelectionDialog_ptr0 = [l:agez] GtkColorSelectionDialog_ptr l
viewtypedef GtkColorSelectionDialog_ptr1 = [l:addr | l > null] GtkColorSelectionDialog_ptr l

viewtypedef GtkDialog_ptr (l:addr) = gobjptr (GtkDialog, l)
viewtypedef GtkDialog_ptr0 = [l:agez] GtkDialog_ptr l
viewtypedef GtkDialog_ptr1 = [l:addr | l > null] GtkDialog_ptr l

viewtypedef GtkDrawingArea_ptr (l:addr) = gobjptr (GtkDrawingArea, l)
viewtypedef GtkDrawingArea_ptr0 = [l:agez] GtkDrawingArea_ptr l
viewtypedef GtkDrawingArea_ptr1 = [l:addr | l > null] GtkDrawingArea_ptr l

viewtypedef GtkEntry_ptr (l:addr) = gobjptr (GtkEntry, l)
viewtypedef GtkEntry_ptr0 = [l:agez] GtkEntry_ptr l
viewtypedef GtkEntry_ptr1 = [l:addr | l > null] GtkEntry_ptr l

viewtypedef GtkFileSelection_ptr (l:addr) = gobjptr (GtkFileSelection, l)
viewtypedef GtkFileSelection_ptr0 = [l:agez] GtkFileSelection_ptr l
viewtypedef GtkFileSelection_ptr1 = [l:addr | l > null] GtkFileSelection_ptr l

viewtypedef GtkFileChooserDialog_ptr (l:addr) = gobjptr (GtkFileChooserDialog, l)
viewtypedef GtkFileChooserDialog_ptr0 = [l:agez] GtkFileChooserDialog_ptr l
viewtypedef GtkFileChooserDialog_ptr1 = [l:addr | l > null] GtkFileChooserDialog_ptr l

viewtypedef GtkFrame_ptr (l:addr) = gobjptr (GtkFrame, l)
viewtypedef GtkFrame_ptr0 = [l:agez] GtkFrame_ptr l
viewtypedef GtkFrame_ptr1 = [l:addr | l > null] GtkFrame_ptr l

viewtypedef GtkHBox_ptr (l:addr) = gobjptr (GtkHBox, l)
viewtypedef GtkHBox_ptr0 = [l:agez] GtkHBox_ptr l
viewtypedef GtkHBox_ptr1 = [l:addr | l > null] GtkHBox_ptr l

viewtypedef GtkHRuler_ptr (l:addr) = gobjptr (GtkHRuler, l)
viewtypedef GtkHRuler_ptr0 = [l:agez] GtkHRuler_ptr l
viewtypedef GtkHRuler_ptr1 = [l:addr | l > null] GtkHRuler_ptr l

viewtypedef GtkHScale_ptr (l:addr) = gobjptr (GtkHScale, l)
viewtypedef GtkHScale_ptr0 = [l:agez] GtkHScale_ptr l
viewtypedef GtkHScale_ptr1 = [l:addr | l > null] GtkHScale_ptr l

viewtypedef GtkHScrollbar_ptr (l:addr) = gobjptr (GtkHScrollbar, l)
viewtypedef GtkHScrollbar_ptr0 = [l:agez] GtkHScrollbar_ptr l
viewtypedef GtkHScrollbar_ptr1 = [l:addr | l > null] GtkHScrollbar_ptr l

viewtypedef GtkHSeparator_ptr (l:addr) = gobjptr (GtkHSeparator, l)
viewtypedef GtkHSeparator_ptr0 = [l:agez] GtkHSeparator_ptr l
viewtypedef GtkHSeparator_ptr1 = [l:addr | l > null] GtkHSeparator_ptr l

viewtypedef GtkImageMenuItem_ptr (l:addr) = gobjptr (GtkImageMenuItem, l)
viewtypedef GtkImageMenuItem_ptr0 = [l:agez] GtkImageMenuItem_ptr l
viewtypedef GtkImageMenuItem_ptr1 = [l:addr | l > null] GtkImageMenuItem_ptr l

viewtypedef GtkLabel_ptr (l:addr) = gobjptr (GtkLabel, l)
viewtypedef GtkLabel_ptr0 = [l:agez] GtkLabel_ptr l
viewtypedef GtkLabel_ptr1 = [l:addr | l > null] GtkLabel_ptr l

viewtypedef GtkMenu_ptr (l:addr) = gobjptr (GtkMenu, l)
viewtypedef GtkMenu_ptr0 = [l:agez] GtkMenu_ptr l
viewtypedef GtkMenu_ptr1 = [l:addr | l > null] GtkMenu_ptr l

viewtypedef GtkMenuBar_ptr (l:addr) = gobjptr (GtkMenuBar, l)
viewtypedef GtkMenuBar_ptr0 = [l:agez] GtkMenuBar_ptr l
viewtypedef GtkMenuBar_ptr1 = [l:addr | l > null] GtkMenuBar_ptr l

viewtypedef GtkMenuItem_ptr (l:addr) = gobjptr (GtkMenuItem, l)
viewtypedef GtkMenuItem_ptr0 = [l:agez] GtkMenuItem_ptr l
viewtypedef GtkMenuItem_ptr1 = [l:addr | l > null] GtkMenuItem_ptr l

viewtypedef GtkMenuShell_ptr (l:addr) = gobjptr (GtkMenuShell, l)
viewtypedef GtkMenuShell_ptr0 = [l:agez] GtkMenuShell_ptr l
viewtypedef GtkMenuShell_ptr1 = [l:addr | l > null] GtkMenuShell_ptr l

viewtypedef GtkOptionMenu_ptr (l:addr) = gobjptr (GtkOptionMenu, l)
viewtypedef GtkOptionMenu_ptr0 = [l:agez] GtkOptionMenu_ptr l
viewtypedef GtkOptionMenu_ptr1 = [l:addr | l > null] GtkOptionMenu_ptr l

viewtypedef GtkRadioButton_ptr (l:addr) = gobjptr (GtkRadioButton, l)
viewtypedef GtkRadioButton_ptr0 = [l:agez] GtkRadioButton_ptr l
viewtypedef GtkRadioButton_ptr1 = [l:addr | l > null] GtkRadioButton_ptr l

viewtypedef GtkSeparatorMenuItem_ptr (l:addr) = gobjptr (GtkSeparatorMenuItem, l)
viewtypedef GtkSeparatorMenuItem_ptr0 = [l:agez] GtkSeparatorMenuItem_ptr l
viewtypedef GtkSeparatorMenuItem_ptr1 = [l:addr | l > null] GtkSeparatorMenuItem_ptr l

viewtypedef GtkSpinButton_ptr (l:addr) = gobjptr (GtkSpinButton, l)
viewtypedef GtkSpinButton_ptr0 = [l:agez] GtkSpinButton_ptr l
viewtypedef GtkSpinButton_ptr1 = [l:addr | l > null] GtkSpinButton_ptr l

viewtypedef GtkStatusbar_ptr (l:addr) = gobjptr (GtkStatusbar, l)
viewtypedef GtkStatusbar_ptr0 = [l:agez] GtkStatusbar_ptr l
viewtypedef GtkStatusbar_ptr1 = [l:addr | l > null] GtkStatusbar_ptr l

viewtypedef GtkTable_ptr (l:addr) = gobjptr (GtkTable, l)
viewtypedef GtkTable_ptr0 = [l:agez] GtkTable_ptr l
viewtypedef GtkTable_ptr1 = [l:addr | l > null] GtkTable_ptr l

viewtypedef GtkTextView_ptr (l:addr) = gobjptr (GtkTextView, l)
viewtypedef GtkTextView_ptr0 = [l:agez] GtkTextView_ptr l
viewtypedef GtkTextView_ptr1 = [l:addr | l > null] GtkTextView_ptr l

viewtypedef GtkToggleButton_ptr (l:addr) = gobjptr (GtkToggleButton, l)
viewtypedef GtkToggleButton_ptr0 = [l:agez] GtkToggleButton_ptr l
viewtypedef GtkToggleButton_ptr1 = [l:addr | l > null] GtkToggleButton_ptr l

viewtypedef GtkVBox_ptr (l:addr) = gobjptr (GtkVBox, l)
viewtypedef GtkVBox_ptr0 = [l:agez] GtkVBox_ptr l
viewtypedef GtkVBox_ptr1 = [l:addr | l > null] GtkVBox_ptr l

viewtypedef GtkVRuler_ptr (l:addr) = gobjptr (GtkVRuler, l)
viewtypedef GtkVRuler_ptr0 = [l:agez] GtkVRuler_ptr l
viewtypedef GtkVRuler_ptr1 = [l:addr | l > null] GtkVRuler_ptr l

viewtypedef GtkVScale_ptr (l:addr) = gobjptr (GtkVScale, l)
viewtypedef GtkVScale_ptr0 = [l:agez] GtkVScale_ptr l
viewtypedef GtkVScale_ptr1 = [l:addr | l > null] GtkVScale_ptr l

viewtypedef GtkVScrollbar_ptr (l:addr) = gobjptr (GtkVScrollbar, l)
viewtypedef GtkVScrollbar_ptr0 = [l:agez] GtkVScrollbar_ptr l
viewtypedef GtkVScrollbar_ptr1 = [l:addr | l > null] GtkVScrollbar_ptr l

viewtypedef GtkVSeparator_ptr (l:addr) = gobjptr (GtkVSeparator, l)
viewtypedef GtkVSeparator_ptr0 = [l:agez] GtkVSeparator_ptr l
viewtypedef GtkVSeparator_ptr1 = [l:addr | l > null] GtkVSeparator_ptr l

// viewtypedef GtkWidget_ptr (l:addr) = gobjptr (GtkWidget, l)

viewtypedef GtkWindow_ptr (l:addr) = gobjptr (GtkWindow, l)
viewtypedef GtkWindow_ptr0 = [l:agez] GtkWindow_ptr l
viewtypedef GtkWindow_ptr1 = [l:addr | l > null] GtkWindow_ptr l

(* ****** ****** *)

objcls GtkAccelGroup = { super: GObject}
viewtypedef GtkAccelGroup_ptr (l:addr) = gobjptr (GtkAccelGroup, l)
viewtypedef GtkAccelGroup_ptr0 = [l:agez] GtkAccelGroup_ptr l
viewtypedef GtkAccelGroup_ptr1 = [l:addr | l > null] GtkAccelGroup_ptr l

(* ****** ****** *)

objcls GtkFileChooser = { super: GInterface}
viewtypedef GtkFileChooser_ptr (l:addr) = gobjptr (GtkFileChooser, l)
viewtypedef GtkFileChooser_ptr0 = [l:agez] GtkFileChooser_ptr l
viewtypedef GtkFileChooser_ptr1 = [l:addr | l > null] GtkFileChooser_ptr l

(* ****** ****** *)

objcls GtkTextBuffer = { super: GObject }
viewtypedef GtkTextBuffer_ptr (l:addr) = gobjptr (GtkTextBuffer, l)
viewtypedef GtkTextBuffer_ptr0 = [l:agez] GtkTextBuffer_ptr l
viewtypedef GtkTextBuffer_ptr1 = [l:addr | l > null] GtkTextBuffer_ptr l

objcls GtkTextTag = { super: GObject }
viewtypedef GtkTextTag_ptr (l:addr) = gobjptr (GtkTextTag, l)
viewtypedef GtkTextTag_ptr0 = [l:agez] GtkTextTag_ptr l
viewtypedef GtkTextTag_ptr1 = [l:addr | l > null] GtkTextTag_ptr l

objcls GtkTextTagTable = { super: GObject }
viewtypedef GtkTextTagTable_ptr (l:addr) = gobjptr (GtkTextTagTable, l)
viewtypedef GtkTextTagTable_ptr0 = [l:agez] GtkTextTagTable_ptr l
viewtypedef GtkTextTagTable_ptr1 = [l:addr | l > null] GtkTextTagTable_ptr l

abst@ype GtkTextIter = $extype "GtkTextIter" // opaque

(* ****** ****** *)

#include "contrib/GTK/SATS/gtk/gtkenums.sats"
#include "contrib/GTK/SATS/gtk/gtkstock.sats"
#include "contrib/GTK/SATS/gtk/gtktypeutils.sats"

(* ****** ****** *)

#include "contrib/GTK/SATS/gtk/gtkaccelgroup.sats"

(* ****** ****** *)

#include "contrib/GTK/SATS/gtk/gtktextbuffer.sats"
#include "contrib/GTK/SATS/gtk/gtktextiter.sats"
#include "contrib/GTK/SATS/gtk/gtktexttag.sats"
#include "contrib/GTK/SATS/gtk/gtktexttagtable.sats"

(* ****** ****** *)

#include "contrib/GTK/SATS/gtk/gtkfilechooser.sats" // GInterface

(* ****** ****** *)

#include "contrib/GTK/SATS/gtk/gtkadjustment.sats"
#include "contrib/GTK/SATS/gtk/gtkalignment.sats"
#include "contrib/GTK/SATS/gtk/gtkarrow.sats"
#include "contrib/GTK/SATS/gtk/gtkbox.sats"
#include "contrib/GTK/SATS/gtk/gtkbutton.sats"
#include "contrib/GTK/SATS/gtk/gtkcheckbutton.sats"
#include "contrib/GTK/SATS/gtk/gtkcontainer.sats"
#include "contrib/GTK/SATS/gtk/gtkcolorsel.sats"
#include "contrib/GTK/SATS/gtk/gtkcolorseldialog.sats"
#include "contrib/GTK/SATS/gtk/gtkdialog.sats"
#include "contrib/GTK/SATS/gtk/gtkdrawingarea.sats"
#include "contrib/GTK/SATS/gtk/gtkentry.sats"
#include "contrib/GTK/SATS/gtk/gtkfilesel.sats" // DEPRECATED!!!
#include "contrib/GTK/SATS/gtk/gtkfilechooserdialog.sats"
#include "contrib/GTK/SATS/gtk/gtkframe.sats"
#include "contrib/GTK/SATS/gtk/gtkhbox.sats"
#include "contrib/GTK/SATS/gtk/gtkhruler.sats"
#include "contrib/GTK/SATS/gtk/gtkhscale.sats"
#include "contrib/GTK/SATS/gtk/gtkhseparator.sats"
#include "contrib/GTK/SATS/gtk/gtkhscrollbar.sats"
#include "contrib/GTK/SATS/gtk/gtkimagemenuitem.sats"
#include "contrib/GTK/SATS/gtk/gtklabel.sats"
#include "contrib/GTK/SATS/gtk/gtkmenu.sats"
#include "contrib/GTK/SATS/gtk/gtkmenubar.sats"
#include "contrib/GTK/SATS/gtk/gtkmenuitem.sats"
#include "contrib/GTK/SATS/gtk/gtkmenushell.sats"
#include "contrib/GTK/SATS/gtk/gtkmisc.sats"
#include "contrib/GTK/SATS/gtk/gtkoptionmenu.sats"
#include "contrib/GTK/SATS/gtk/gtkradiobutton.sats"
#include "contrib/GTK/SATS/gtk/gtkrange.sats"
#include "contrib/GTK/SATS/gtk/gtkruler.sats"
#include "contrib/GTK/SATS/gtk/gtkscale.sats"
#include "contrib/GTK/SATS/gtk/gtkscrollbar.sats"
#include "contrib/GTK/SATS/gtk/gtkseparator.sats"
#include "contrib/GTK/SATS/gtk/gtkseparatormenuitem.sats" // <= menuitem
#include "contrib/GTK/SATS/gtk/gtkspinbutton.sats" // <= entry
#include "contrib/GTK/SATS/gtk/gtkstatusbar.sats"
#include "contrib/GTK/SATS/gtk/gtktable.sats" // <= container
#include "contrib/GTK/SATS/gtk/gtktextview.sats" // <= container
#include "contrib/GTK/SATS/gtk/gtktogglebutton.sats"
#include "contrib/GTK/SATS/gtk/gtkvbox.sats"
#include "contrib/GTK/SATS/gtk/gtkvruler.sats"
#include "contrib/GTK/SATS/gtk/gtkvscale.sats"
#include "contrib/GTK/SATS/gtk/gtkvscrollbar.sats"
#include "contrib/GTK/SATS/gtk/gtkvseparator.sats"
#include "contrib/GTK/SATS/gtk/gtkwidget.sats"
#include "contrib/GTK/SATS/gtk/gtkwindow.sats"

(* ****** ****** *)

#include "contrib/GTK/SATS/gtk/gtkmain.sats"

(* ****** ****** *)

(* end of [gtk.sats] *)
