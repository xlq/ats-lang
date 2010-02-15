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
*)

(* ****** ****** *)

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: January, 2010

(* ****** ****** *)

%{#
#include "contrib/X11/CATS/X.cats"
%} // end of [{%#]

(* ****** ****** *)

abst@ype Atom = $extype "Atom" // unsigned long int
abst@ype Mask = $extype "Mask" // unsigned long int
abst@ype VisualID = $extype "VisualID" // unsigned long int
abst@ype Time = $extype "Time" // unsigned long int

(* ****** ****** *)

// [XID] is unsigned long int  

abst@ype XID = $extype "XID"
abst@ype Window = $extype "Window" // = XID
abst@ype Font = $extype "Font" // = XID
abst@ype Pixmap = $extype "Pixmap" // = XID
abst@ype Cursor = $extype "Cursor" // = XID
abst@ype Colormap = $extype "Colormap" // = XID
abst@ype GContext = $extype "GContext" // = XID
abst@ype KeySym = $extype "KeySym" // = XID

//

abst@ype Drawable = $extype "Drawable" // = XID

symintr Drawable

castfn Drawable_of_Window (x: Window): Drawable
overload Drawable with Drawable_of_Window

castfn Drawable_of_Pixmap (x: Pixmap): Drawable
overload Drawable with Drawable_of_Pixmap

(* ****** ****** *)

// EVENT DEFINITIONS 

(*
** Input Event Masks.
** Used as event-mask window attribute and as arguments to Grab requests.
*)

abst@ype InputEventMask_t = lint
fun lor_InputEventMask_InputEventMask
  (x: InputEventMask_t, y: InputEventMask_t): InputEventMask_t
  = "atsctrb_lor_InputEventMask_InputEventMask"
// end of [lor_InputEventMask_InputEventMask]
overload lor with lor_InputEventMask_InputEventMask

macdef NoEventMask = $extval (InputEventMask_t, "NoEventMask")
macdef KeyPressMask = $extval (InputEventMask_t, "KeyPressMask")
macdef KeyReleaseMask = $extval (InputEventMask_t, "KeyReleaseMask")
macdef ButtonPressMask = $extval (InputEventMask_t, "ButtonPressMask")
macdef ButtonReleaseMask = $extval (InputEventMask_t, "ButtonReleaseMask")
macdef EnterWindowMask = $extval (InputEventMask_t, "EnterWindowMask")
macdef LeaveWindowMask = $extval (InputEventMask_t, "LeaveWindowMask")
macdef PointerMotionMask = $extval (InputEventMask_t, "PointerMotionMask")
macdef PointerMotionHintMask = $extval (InputEventMask_t, "PointerMotionHintMask")
macdef Button1MotionMask = $extval (InputEventMask_t, "Button1MotionMask")
macdef Button2MotionMask = $extval (InputEventMask_t, "Button2MotionMask")
macdef Button3MotionMask = $extval (InputEventMask_t, "Button3MotionMask")
macdef Button4MotionMask = $extval (InputEventMask_t, "Button4MotionMask")
macdef Button5MotionMask = $extval (InputEventMask_t, "Button5MotionMask")
macdef ButtonMotionMask = $extval (InputEventMask_t, "ButtonMotionMask")
macdef KeymapStateMask = $extval (InputEventMask_t, "KeymapStateMask")
macdef ExposureMask = $extval (InputEventMask_t, "ExposureMask")
macdef VisibilityChangeMask = $extval (InputEventMask_t, "VisibilityChangeMask")
macdef StructureNotifyMask = $extval (InputEventMask_t, "StructureNotifyMask")
macdef ResizeRedirectMask = $extval (InputEventMask_t, "ResizeRedirectMask")
macdef SubstructureNotifyMask = $extval (InputEventMask_t, "SubstructureNotifyMask")
macdef SubstructureRedirectMask = $extval (InputEventMask_t, "SubstructureRedirectMask")
macdef FocusChangeMask = $extval (InputEventMask_t, "FocusChangeMask")
macdef PropertyChangeMask = $extval (InputEventMask_t, "PropertyChangeMask")
macdef ColormapChangeMask = $extval (InputEventMask_t, "ColormapChangeMask")
macdef OwnerGrabButtonMask = $extval (InputEventMask_t, "OwnerGrabButtonMask")

(* ****** ****** *)

(*
** Event names.
** Used in "type" field in XEvent structures
*)

abst@ype EventType_t = int
fun eq_EventType_EventType (x: EventType_t, y: EventType_t): bool
  = "atsctrb_eq_EventType_EventType"
overload = with eq_EventType_EventType

macdef KeyPress = $extval (EventType_t, "KeyPress")
macdef KeyRelease = $extval (EventType_t, "KeyRelease")
macdef ButtonPress = $extval (EventType_t, "ButtonPress")
macdef ButtonRelease = $extval (EventType_t, "ButtonRelease")
macdef MotionNotify = $extval (EventType_t, "MotionNotify")
macdef EnterNotify = $extval (EventType_t, "EnterNotify")
macdef LeaveNotify = $extval (EventType_t, "LeaveNotify")
macdef FocusIn = $extval (EventType_t, "FocusIn")
macdef FocusOut = $extval (EventType_t, "FocusOut")
macdef KeymapNotify = $extval (EventType_t, "KeymapNotify")
macdef Expose = $extval (EventType_t, "Expose")
macdef GraphicsExpose = $extval (EventType_t, "GraphicsExpose")
macdef NoExpose = $extval (EventType_t, "NoExpose")
macdef VisibilityNotify = $extval (EventType_t, "VisibilityNotify")
macdef CreateNotify = $extval (EventType_t, "CreateNotify")
macdef DestroyNotify = $extval (EventType_t, "DestroyNotify")
macdef UnmapNotify = $extval (EventType_t, "UnmapNotify")
macdef MapNotify = $extval (EventType_t, "MapNotify")
macdef MapRequest = $extval (EventType_t, "MapRequest")
macdef ReparentNotify = $extval (EventType_t, "ReparentNotify")
macdef ConfigureNotify = $extval (EventType_t, "ConfigureNotify")
macdef ConfigureRequest = $extval (EventType_t, "ConfigureRequest")
macdef GravityNotify = $extval (EventType_t, "GravityNotify")
macdef ResizeRequest = $extval (EventType_t, "ResizeRequest")
macdef CirculateNotify = $extval (EventType_t, "CirculateNotify")
macdef CirculateRequest = $extval (EventType_t, "CirculateRequest")
macdef PropertyNotify = $extval (EventType_t, "PropertyNotify")
macdef SelectionClear = $extval (EventType_t, "SelectionClear")
macdef SelectionRequest = $extval (EventType_t, "SelectionRequest")
macdef SelectionNotify = $extval (EventType_t, "SelectionNotify")
macdef ColormapNotify = $extval (EventType_t, "ColormapNotify")
macdef ClientMessage = $extval (EventType_t, "ClientMessage")
macdef MappingNotify = $extval (EventType_t, "MappingNotify")
macdef LASTEvent = $extval (EventType_t, "LASTEvent")

(* ****** ****** *)

(* end of [X.sats] *)
