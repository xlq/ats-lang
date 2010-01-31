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
#include "contrib/X11/CATS/Xlib.cats"
%} // end of [{%#]

(* ****** ****** *)

staload "contrib/X11/SATS/X.sats"

(* ****** ****** *)

absview XFree_v (l:addr) // ticket view for XFree
absview XFree_v (a:viewt@ype, l:addr) // ticket view for XFree
absview XFree_v (a:viewt@ype, n:int, l:addr) // ticket view for XFree

(* ****** ****** *)

// HX-2010-01-22:
// it is just a pointer; it is not reference counted
absviewtype Display_ptr (l:addr) // Display*
viewtypedef Display_ptr0 = [l:addr] Display_ptr l
viewtypedef Display_ptr1 = [l:anz] Display_ptr l

// HX-2010-01-22:
// it is just a pointer; it is not reference counted
absviewtype Screen_ptr (l:addr) // Screen*
viewtypedef Screen_ptr0 = [l:addr] Screen_ptr l
viewtypedef Screen_ptr1 = [l:anz] Screen_ptr l

// it is just a pointer; it is not reference counted
absviewtype Visual_ptr (l:addr) // Visual*
viewtypedef Visual_ptr0 = [l:addr] Visual_ptr l
viewtypedef Visual_ptr1 = [l:anz] Visual_ptr l

(* ****** ****** *)

//
// Chapter 2: Display Functions
//

(* ****** ****** *)

//
// 2.1: opening the display
//

(* ****** ****** *)

fun XOpenDisplay (name: string): Display_ptr0 = "#atsctrb_XOpenDisplay"

fun Display_ptr_is_null {l:addr} (p_dpy: !Display_ptr l): bool (l == null)
  = "atspre_ptr_is_null" // defined in $ATSHOME/prelude/CATS/pointer.cats
fun Display_ptr_isnot_null {l:addr} (p_dpy: !Display_ptr l): bool (l <> null)
  = "atspre_ptr_isnot_null" // defined in $ATSHOME/prelude/CATS/pointer.cats

(* ****** ****** *)

//
// 2.2: obtaining information about display, image formats or screens
//

(* ****** ****** *)

// 2.2.1: display macros

(* ****** ****** *)

fun XAllPlanes (): ulint = "#atsctrb_XAllPlanes"

fun XBlackPixel {l:anz}
  (dpy: !Display_ptr l, nscr: int):<> ulint
  = "#atsctrb_XBlackPixel"
fun XWhitePixel {l:anz}
  (dpy: !Display_ptr l, nscr: int):<> ulint
  = "#atsctrb_XWhitePixel"

fun XConnectionNumber {l:anz} (dpy: !Display_ptr l):<> int
  = "#atsctrb_XConnectionNumber"

fun XDefaultColormap {l:anz}
  (dpy: !Display_ptr l, nscr: int):<> Colormap
  = "#atsctrb_XDefaultColormap"

(* ****** ****** *)

fun XDefaultDepth {l:anz}
  (dpy: !Display_ptr l, nscr: int):<> int
  = "#atsctrb_XDefaultDepth"

// note: for simplifying error handling,
fun XListDepths {l:anz} // [cnt] needs to be set to 0 first!
  (dpy: !Display_ptr l, nscr: int, cnt: &int 0 >> int n)
  : #[la:addr;n:nat] (XFree_v (int, n, la), @[int][n] @ la | ptr la)
  = "#atsctrb_XListDepths"

(* ****** ****** *)

abstype GCref =
  $extype "GC" // this one should never be freed!
fun XDefaultGC {l:anz}
  (dpy: !Display_ptr l, nscr: int): GCref
  = "#atsctrb_XDefaultGC"

(* ****** ****** *)

fun XDefaultRootWindow {l:anz} (dpy: !Display_ptr l): Window
  = "#atsctrb_XDefaultRootWindow"

fun XDefaultScreenOfDisplay
  {l1:anz} (dpy: !Display_ptr l1)
  : [l2:anz] (
    minus (Display_ptr l1, Screen_ptr l2) | Screen_ptr l2
  ) = "#atsctrb_XDefaultScreenOfDisplay"
// end of [XDefaultScreenOfDisplay]

fun XScreenOfDisplay
  {l1:anz} (dpy: !Display_ptr l1, nsrc: int)
  : [l2:anz] (
    minus (Display_ptr l1, Screen_ptr l2) | Screen_ptr l2
  ) = "#atsctrb_XDefaultScreenOfDisplay"
// end of [XDefaultScreenOfDisplay]

fun XDefaultScreen {l:anz} (dpy: !Display_ptr l): int(*nscr*)
  = "#atsctrb_XDefaultScreen"

fun XDefaultVisual
  {l1:anz} (dpy: !Display_ptr l1, nsrc: int)
  : [l2:anz] (
    minus (Display_ptr l1, Visual_ptr l2) | Visual_ptr l2
  ) = "#atsctrb_XDefaultVisual"
// end of [XDefaultVisual]

// number of entries in the default colormap
fun XDisplayCells {l:anz}
  (dpy: !Display_ptr l, nscr: int): int(*ncell*)
  = "#atsctrb_XDisplayCells"

// the depth of the root window
fun XDisplayPlanes {l:anz}
  (dpy: !Display_ptr l, nscr: int): int(*depth*)
  = "#atsctrb_XDisplayPlanes"

// the name passed to XOpenDisplay
fun XDisplayString {l:anz} (dpy: !Display_ptr l): string
  = "#atsctrb_XDisplayString"

(* ****** ****** *)

fun XMaxRequestSize {l:anz}
  (dpy: !Display_ptr l): lint // in 4-byte units
  = "#atsctrb_XMaxRequestSize"

// the full serial number for the last processed request
fun XLastKnownRequestProcessed {l:anz} (dpy: !Display_ptr l): ulint
  = "#atsctrb_XLastKnownRequestProcessed"

// the full serial number to be used for the next request
fun XNextRequest {l:anz} (dpy: !Display_ptr l): ulint
  = "#atsctrb_XNextRequest"

(* ****** ****** *)

fun XProtocolVersion {l:anz} (dpy: !Display_ptr l): int
  = "#atsctrb_XProtocolVersion"

fun XProtocolRevision {l:anz} (dpy: !Display_ptr l): int
  = "#atsctrb_XProtocolRevision"

(* ****** ****** *)

// the length of the event queue for [dpy]
fun XQLength {l:anz} (dpy: !Display_ptr l): int
  = "#atsctrb_XQLength"

(* ****** ****** *)

fun XRootWindow {l:anz} (dpy: !Display_ptr l, nscr: int): Window
  = "#atsctrb_XRootWindow"

fun XScreenCount {l:anz} (dpy: !Display_ptr l): int
  = "#atsctrb_XScreenCount"

fun XServerVendor {l:anz} (dpy: !Display_ptr l): string
  = "#atsctrb_XServerVendor"

fun XVendorRelease {l:anz} (dpy: !Display_ptr l): int
  = "#atsctrb_XVendorRelease"

(* ****** ****** *)

// 2.2.2: image format functions and macros

(* ****** ****** *)

typedef XPixmapFormatValues =
  $extype_struct "XPixmapFormatValues" of {
  depth= int, bits_per_pixel= int, scanline_pad= int
} // end of [XPixmapFormatValues]

fun XListPixmapFormats {l:anz}
  (dpy: !Display_ptr l, n: &int 0 >> int n)
  : #[la:addr;n:nat] (
    XFree_v (XPixmapFormatValues, n, la)
  , array_v (XPixmapFormatValues, n, la)
  | ptr la
  ) = "#atsctrb_XListPixmapFormats"

macdef LSBFirst = $extval (int, "LSBFirst")
macdef MSBFirst = $extval (int, "MSBFirst")

fun XImageByteOrder {l:anz} (dpy: !Display_ptr l): int
  = "#atsctrb_XImageByteOrder"

fun XBitmapUnit {l:anz} (dpy: !Display_ptr l): int
  = "#atsctrb_XBitmapUnit"

fun XBitmapOrder {l:anz} (dpy: !Display_ptr l): int
  = "#atsctrb_XBitmapOrder"

fun XBitmapPad {l:anz} (dpy: !Display_ptr l): int
  = "#atsctrb_XBitmapPad"

fun XDisplayHeight {l:anz} (dpy: !Display_ptr l, nscr: int): int
  = "#atsctrb_XDisplayHeight"

fun XDisplayHeightMM {l:anz} (dpy: !Display_ptr l, nscr: int): int
  = "#atsctrb_XDisplayHeightMM"

fun XDisplayWidth {l:anz} (dpy: !Display_ptr l, nscr: int): int
  = "#atsctrb_XDisplayWidth"

fun XDisplayWidthMM {l:anz} (dpy: !Display_ptr l, nscr: int): int
  = "#atsctrb_XDisplayWidthMM"

(* ****** ****** *)

// 2.2.3: screen information macros

(* ****** ****** *)

fun XBlackPixelOfScreen {l:anz} (scr: !Screen_ptr l): ulint
  = "#atsctrb_XBlackPixelOfScreen"

fun XWhitePixelOfScreen {l:anz} (scr: !Screen_ptr l): ulint
  = "#atsctrb_XWhitePixelOfScreen"

fun XCellsOfScreen {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XCellsOfScreen"

fun XDefaultColormapOfScreen {l:anz} (scr: !Screen_ptr l): Colormap
  = "#atsctrb_XDefaultColormapOfScreen"

fun XDefaultDepthOfScreen {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XDefaultDepthOfScreen"

fun XDefaultGCOfScreen {l:anz} (scr: !Screen_ptr l): GCref
  = "#atsctrb_XDefaultGCOfScreen"

//
// the function returns WhenMapped, NotUseful or Always
//
fun XDoesBackingStore {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XDoesBackingStore"

fun XDoesSaveUnders {l:anz} (scr: !Screen_ptr l): bool
  = "#atsctrb_XDoesSaveUnders"

fun XScreenNumberOfScreen {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XScreenNumberofScreen"

fun XEventMaskOfScreen {l:anz} (scr: !Screen_ptr l): lint
  = "#atsctrb_XEventMaskOfScreen"

fun XWidthOfScreen {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XWidthOfScreen"

fun XWidthMMOfScreen {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XWidthMMOfScreen"

fun XHeightOfScreen {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XHeightOfScreen"

fun XHeightMMOfScreen {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XHeightMMOfScreen"

fun XMaxCmapsOfScreen {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XMaxCmapsOfScreen"

fun XMinCmapsOfScreen {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XMinCmapsOfScreen"

fun XPlanesOfScreen {l:anz} (scr: !Screen_ptr l): int
  = "#atsctrb_XPlanesOfScreen"

fun XRootWindowOfScreen {l:anz} (scr: !Screen_ptr l): Window
  = "#atsctrb_XRootWindowOfScreen"

(* ****** ****** *)

//
// 2.3: generating a NoOperation protocol request
//

(* ****** ****** *)

fun XNoOp {l:anz} (dpy: Display_ptr l): void
  = "#atsctrb_XNoOp"

(* ****** ****** *)

//
// 2.4: freeing client-created data
//

(* ****** ****** *)

fun XFree0 {a:viewt@ype} {l:addr}
  (pf1: XFree_v l, pf2: a? @ l | p: ptr l): void
  = "#atsctrb_XFree"

fun XFree1 {a:viewt@ype} {l:addr}
  (pf1: XFree_v (a, l), pf2: a? @ l | p: ptr l): void
  = "#atsctrb_XFree"

fun XFree2 {a:viewt@ype} {n:nat} {l:addr}
  (pf1: XFree_v (a, n, l), pf2: array_v (a?, n, l) | p: ptr l): void
  = "#atsctrb_XFree"

symintr XFree
overload XFree with XFree0
overload XFree with XFree1
overload XFree with XFree2

(* ****** ****** *)

//
// 2.5: closing the display
//

fun XCloseDisplay (dpy: Display_ptr1): void = "#atsctrb_XCloseDisplay"

abst@ype close_mode_t = int
macdef DestroyAll = $extval (close_mode_t, "DestroyAll")
macdef RetainPermanent = $extval (close_mode_t, "RetainPermanent")
macdef RetainTemporary = $extval (close_mode_t, "RetainTemporary")

// [XSetCloseDownMode] may generate a BadValue error
fun XSetCloseDownMode {l:anz} (dpy: Display_ptr l, mode: close_mode_t): void

(* ****** ****** *)

//
// Chapter 3: Window Functions
//

(* ****** ****** *)

//
// 3.1: visual types
//

fun XVisualIDFromVisual {l:anz} (visual: !Visual_ptr l): VisualID
  = "#atsctrb_XVisualIDFromVisual"
  
(* ****** ****** *)

//
// 3.2: window attributes
//

typedef XSetWindowAttributes =
  $extype_struct "XSetWindowAttributes" of {
  background_pixmap= Pixmap
, background_pixel= ulint
, border_pixmap= Pixmap
, border_pixel= ulint
, bit_gravity= int
, win_gravity= int
, backing_store= int
, backing_planes= ulint
, backing_pixel= ulint
, save_under= bool
, event_mask= lint
, do_not_propagate_mask= lint
, override_redirect= bool
, colormap= Colormap
, cursor= Cursor
} // end of [XSetWindowAttributes]

(* ****** ****** *)

//
// 3.3: creating windows
//

fun XCreateWindow {ld,lv:anz} (
    dpy: !Display_ptr ld
  , parent: Window
  , x: int, y: int
  , width: uint, height: uint
  , border_width: uint
  , depth: uint // can [depth] be negative?
  , _class: uint
  , visual: !Visual_ptr lv
  , valuemask: ulint
  , attr: &XSetWindowAttributes
  ) : Window
  = "#atsctrb_XCreateWindow"
// end of [XCreateWindow]

fun XCreateSimpleWindow {ld:anz} (
    dpy: !Display_ptr ld
  , parent: Window
  , x: int, y: int
  , width: uint, height: uint
  , border_width: uint
  , border: ulint
  , background: ulint
  ) : Window
  = "#atsctrb_XCreateSimpleWindow"
// end of [XCreateSimpleWindow]

(* ****** ****** *)

//
// 3.4: destroying windows
//

fun XDestroyWindow {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XDestroyWindow"

fun XDestroySubwindows {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XDestroyWindow"

(* ****** ****** *)

//
// 3.5: mapping windows
//

fun XMapWindow {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XMapWindow"

fun XMapRaised {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XMapRaised"

fun XMapSubwindows {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XMapSubwindows"

(* ****** ****** *)

//
// 3.6: unmapping windows
//

fun XUnmapWindow {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XUnmapWindow"

fun XUnmapSubwindows {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XUnmapSubwindows"

(* ****** ****** *)

//
// 3.7: configuring windows
//

typedef XWindowChanges =
  $extype_struct "XWindowChanges" of {
  x= int, y= int
, width= int, height= int
, border_width= int
, sibling= Window
, stack_mode= int
} // end of [XWindowChanges]

fun XConfigureWindow {l:addr} (
    dpy: !Display_ptr l, win: Window, valmask: uint, values: &XWindowChanges
  ) : void
  = "#atsctrb_XConfigureWindow"

fun XMoveWindow {l:addr}
  (dpy: !Display_ptr l, win: Window, x: int, y: int): void
  = "#atsctrb_XMoveWindow"

fun XResizeWindow {l:addr}
  (dpy: !Display_ptr l, win: Window, width: uint, height: uint): void
  = "#atsctrb_XResizeWindow"

fun XMoveResizeWindow {l:addr} (
    dpy: !Display_ptr l, win: Window, x: int, y: int, width: uint, height: uint
  ) : void
  = "#atsctrb_XMoveResizeWindow"

fun XSetWindowBorderWidth {l:addr}
  (dpy: !Display_ptr l, win: Window, border_width: uint): void
  = "#atsctrb_XSetWindowBorderWidth"

(* ****** ****** *)

//
// 3.8: changing windows stacking order
//

fun XRaiseWindow {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XRaiseWindow"

fun XLowerWindow {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XLowerWindow"

fun XCirculateSubwindows {l:anz}
  (dpy: !Display_ptr l, win: Window, dir: int): void
  = "#atsctrb_XCirculateSubwindows"

fun XCirculateSubwindowsUp {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XCirculateSubwindowsUp"

fun XCirculateSubwindowsDown {l:anz}
  (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XCirculateSubwindowsDown"

fun XRestackWindows {l:anz} {n:nat}
  (dpy: !Display_ptr l, wins: &(@[Window][n]), nwin: int n): void
  = "#atsctrb_XRestackWindows"

(* ****** ****** *)

//
// 3.9: changing windows attributes
//

fun XChangeWindowAttributes {l:anz} (
    dpy: !Display_ptr l, win: Window, valmask: ulint, attr: &XSetWindowAttributes
  ) : void
  = "#atsctrb_XChangeWindowAttributes"

fun XSetWindowBackground {l:anz}
  (dpy: !Display_ptr l, win: Window, bg_pixel: ulint): void
  = "#atsctrb_XSetWindowBackground"

fun XSetWindowBackgroundPixmap {l:anz}
  (dpy: !Display_ptr l, win: Window, bg_pixmap: Pixmap): void
  = "#atsctrb_XSetWindowBackgroundPixmap"

fun XSetWindowBorder {l:anz}
  (dpy: !Display_ptr l, win: Window, bd_pixel: ulint): void
  = "#atsctrb_XSetWindowBorder"

fun XSetWindowBorderPixmap {l:anz}
  (dpy: !Display_ptr l, win: Window, bd_pixmap: Pixmap): void
  = "#atsctrb_XSetWindowBorderPixmap"

fun XSetWindowColormap {l:anz}
  (dpy: !Display_ptr l, win: Window, colormap: Colormap): void
  = "#atsctrb_XSetWindowColormap"

fun XDefineCursor {l:anz}
  (dpy: !Display_ptr l, win: Window, cursor: Cursor): void
  = "#atsctrb_XDefineCursor"

fun XUndefineCursor {l:anz} (dpy: !Display_ptr l, win: Window): void
  = "#atsctrb_XUndefineCursor"

(* ****** ****** *)

//
// Chapter 4: Window Information Functions
//

(* ****** ****** *)

abst@ype Status = $extype "Status" // = int
castfn int_of_Status (x: Status):<> int
overload int_of with int_of_Status

fun XQueryTree {l:anz} (
    dpy: !Display_ptr l
  , win: Window
  , root: &Window? >> Window
  , parent: &Window? >> Window
  , children: &ptr? >> ptr l
  , nchilren: &int >> int n
  ) : #[l:addr;n:nat] (
    XFree_v (Window, n, l), array_v (Window, n, l) | Status
  ) = "#atsctrb_XQueryTree"
// end of [XQueryTree]

typedef XWindowAttributes =
  $extype_struct "XWindowAttributes" of {
  x= int, y= int
, width= uint, height= uint
, border_width= uint
, depth= int
// , visual= Visual_ptr1
, root= Window
, _class= int
, bit_gravity= int
, win_gravity= int
, backing_store= int
, backing_planes= ulint
, backing_pixel= ulint
, save_under= bool
, colormap= Colormap
, map_installed= bool
, map_state= int
, all_event_mask= lint
, your_event_mask= lint
, do_not_propagate_mask= lint
, override_redirect= bool
// , screen= Screen_ptr1
} // end of [XWindowAttributes]

fun XGetWindowAttributes {l:anz} (
    dpy: !Display_ptr l, win: Window
  , attr: &XWindowAttributes? >> XWindowAttributes
  ) : Status
  = "#atsctrb_XGetWindowAttributes"

fun XGetGeometry {l:anz} (
    dpy: !Display_ptr l, drw: Drawable
  , root: &Window? >> Window
  , x: &int? >> int, y: &int? >> int
  , width: &uint? >> uint, height: &uint? >> uint
  , border_width: &uint? >> uint
  , depth: &uint? >> uint
  ) : Status
  = "#atsctrb_XGetWindowAttributes"

(* ****** ****** *)

//
// 4.2: translating screen coordinates
//

fun XTranslateCoordinates {l:anz} (
    dpy: !Display_ptr l
  , win_src: Window, win_dst: Window
  , x_src: int, y_src: int
  , x_dst: &int? >> int, y_dst: &int? >> int
  , child: &Window? >> Window
  ) : bool
  = "#atsctrb_XTranslateCoordinates"

fun XQueryPointer {l:anz} (
    dpy: !Display_ptr l
  , win: Window
  , root: &Window? >> Window, child: &Window? >> Window
  , x_root: &int? >> int, y_root: &int? >> int
  , x_win: &int? >> int, y_win: &int? >> int
  , mask: &uint? >> uint
  ) : bool
  = "#atsctrb_XQueryPointer"

(* ****** ****** *)

//
// 4.3: properties and atoms
//

fun XInternAtom {l:anz} (
    dpy: !Display_ptr l, atom_name: string, only_if_exists: bool
  ) : Atom = "#atsctrb_XInternAtom"
// end of [XInternAtom]

fun XGetAtomName {l:anz}
  (dpy: !Display_ptr l, atom: Atom)
  : [l_str:addr] (XFree_v l, strbuf_v l_str | ptr l_str)
  = "#atsctrb_XGetAtomName"
// end of [XGetAtomName]

(* ****** ****** *)

//
// 4.4: obtaining and changing window properties
//

(* ****** ****** *)

//
// Chapter 5: Pixmap and Cursor Functions
//

(* ****** ****** *)

//
// 5.1: creating and freeing pixmaps
//

fun XCreatePixmap {l:anz} (
    dpy: !Display_ptr l
  , drw: Drawable, width: uint, height: uint, depth: uint
  ) : Pixmap
  = "#atsctrb_XCreatePixmap"

fun XFreePixmap
  {l:anz} (dpy: !Display_ptr l, pixmap: Pixmap): void
  = "#atsctrb_XFreePixmap"

(* ****** ****** *)

//
// 5.2: creating, recoloring and freeing cursors
//

fun XCreateFontCursor
  {l:anz} (dpy: !Display_ptr l, shape: uint) : Cursor
  = "#atsctrb_XCreateFontCursor"

fun XFreeCursor
  {l:anz} (dpy: !Display_ptr l, cursor: Cursor): void
  = "#atsctrb_XFreeCursor"

(* ****** ****** *)

//
// Chapter 6: Color Management Functions
//

(* ****** ****** *)

// 6.1: color structures

typedef XColor =
  $extype_struct "XColor" of {
  pixel= ulint
, red= usint, green= usint, blue= usint
, flags= char, pad= char
} // end of [XColor]

(* ****** ****** *)

// 6.4: creating, copying and destroying

fun XCreateColormap {l1,l2:addr} (
    dsp: !Display_ptr l1
  , win: Window, visual: !Visual_ptr l2, alloc: int
  ) : Colormap
  = "#atsctrb_XCreateColormap"

fun XCopyColormapAndFree {l:addr}
  (dpy: !Display_ptr l, colormap: Colormap): void
  = "#atsctrb_XCopyColormapAndFree"

fun XFreeColormap {l:addr}
  (dpy: !Display_ptr l, colormap: Colormap): void
  = "#atsctrb_XFreeColormap"

(* ****** ****** *)

//
// Chapter 11: Event Handling functions
//

(* ****** ****** *)

// 11.1: selecting events

fun XSelectInput {l:anz}
  (dpy: !Display_ptr l, win: Window, eventmask: lint): void
  = "#atsctrb_XSelectInput"

(* ****** ****** *)

// 11.2: handling the output buffer

fun XFlush {l:anz} (dpy: !Display_ptr l): void
  = "#atsctrb_XFlush"

fun XSync {l:anz} (dpy: !Display_ptr l, discard: bool): void
  = "#atsctrb_XSync"

(* ****** ****** *)

(* end of [Xlib.sats] *)
