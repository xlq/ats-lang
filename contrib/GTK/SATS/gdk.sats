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
#include "contrib/GTK/CATS/gdk.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staload at run-time

(* ****** ****** *)

staload GLIB = "contrib/glib/SATS/glib.sats"
stadef gint = $GLIB.gint
stadef guint = $GLIB.guint
stadef gint8 = $GLIB.gint8
stadef guint8 = $GLIB.guint8
stadef guint16 = $GLIB.guint16
stadef guint32 = $GLIB.guint32
stadef gpointer = $GLIB.gpointer

(* ****** ****** *)

staload GOBJ = "contrib/glib/SATS/glib-object.sats"
stadef GObject = $GOBJ.GObject
stadef gobjptr = $GOBJ.gobjptr

(* ****** ****** *)

absview GdkFree_v (l:addr) // for free GDK resources

(* ****** ****** *)

//
// class hierarchy for GDK
//
objcls GdkObject = { super: GObject }
  objcls GdkDrawable = { super: GdkObject }
    objcls GdkWindow = { super: GdkDrawable }
  // end of [GdkDrawable]
// end of [GdkObject]

(* ****** ****** *)

viewtypedef GdkWindow_ptr (l:addr) = gobjptr (GdkWindow, l)
viewtypedef GdkWindow_ptr0 = [l:agez] GdkWindow_ptr l
viewtypedef GdkWindow_ptr1 = [l:addr | l > null] GdkWindow_ptr l

(* ****** ****** *)

#include "contrib/GTK/SATS/gdk/gdktypes.sats"

(* ****** ****** *)

#include "contrib/GTK/SATS/gdk/gdkcolor.sats"
#include "contrib/GTK/SATS/gdk/gdkevents.sats"

(* ****** ****** *)

(* end of [gdk.sats] *)
