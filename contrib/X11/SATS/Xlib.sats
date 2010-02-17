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

// it is just a pointer; it is not reference counted
absviewtype GCptr (l:addr)  = $extype "GC" // *GC = _XGC
viewtypedef GCptr = [l:addr] GCptr l
abstype GCref = $extype "GC" // this one should never be freed!

(* ****** ****** *)

//
// Chapter 2: Display Functions
//

(* ****** ****** *)

//
// 2.1: opening the display
//

(* ****** ****** *)

fun XOpenDisplay (name: Stropt): Display_ptr0 = "#atsctrb_XOpenDisplay"

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

fun XDefaultGC {l:anz} (dpy: !Display_ptr l, nscr: int): GCref
  = "#atsctrb_XDefaultGC"
// end of [XDefaultGC]

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

fun XNoOp {l:anz} (dpy: !Display_ptr l): void
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
  , border_width: uint // in pixels
  , border: ulint // border pixel value
  , background: ulint // background pixel value
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
// end of [XFreePixmap]

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

fun XCreateColormap {l1,l2:anz} (
    dsp: !Display_ptr l1
  , win: Window, visual: !Visual_ptr l2, alloc: int
  ) : Colormap
  = "#atsctrb_XCreateColormap"

fun XCopyColormapAndFree {l:anz}
  (dpy: !Display_ptr l, colormap: Colormap): void
  = "#atsctrb_XCopyColormapAndFree"

fun XFreeColormap {l:anz}
  (dpy: !Display_ptr l, colormap: Colormap): void
  = "#atsctrb_XFreeColormap"

(* ****** ****** *)

// 6.5: Mapping Color Names to Values

fun XLookupColor {l:anz} (
    dpy: !Display_ptr l
  , colormap: Colormap, color_name: string
  , exact_def: &XColor? >> XColor, screen_def: &XColor? >> XColor 
  ) : Status // nonzero if the name is resolved
  = "#atsctrb_XLookupColor"
// end of [XLookupColor]

fun XParseColor {l:anz} (
    dpy: !Display_ptr l
  , colormap: Colormap
  , spec: string
  , exact_def: &XColor? >> XColor
  ) : Status // nonzero if the name is resolved
  = "#atsctrb_XParseColor"
// end of [XParseColor]

(*
fun XcmsLookupColor (...)
*)

(* ****** ****** *)

// 6.6: Allocating and Freeing Color Cells

fun XAllocColor {l:anz} (
    dpy: !Display_ptr l
  , colormap: Colormap, screen_in_out: &XColor >> XColor
  ) : Status
  = "#atsctrb_XAllocColor"
// end of [XAllocColor]

(*
fun XcmsAllocColor (...)
*)

fun XAllocNamedColor {l:anz} (
    dpy: !Display_ptr l
  , colormap: Colormap
  , color_name: string
  , screen_def: &XColor? >> XColor
  , exact_def: &XColor? >> XColor
  ) : Status
  = "#atsctrb_XAllocNamedColor"
// end of [XAllocNamedColor]

(*
fun XcmsAllocNamedColor (...)
*)

(*
fun XAllocColorCells (...)
fun XAllocColorPlanes (...)
*)

(*
fun XFreeColors (...)
*)

(* ****** ****** *)

// 6.7: Modifying and Querying Colormap Cells

fun XStoreColor {l:anz} (
    dpy: !Display_ptr l, colormap: Colormap, color: &XColor
  ) : void = "#atsctrb_XStoreColor"
// end of [XStoreColor]

fun XStoreColors {l:anz} {n:nat} (
    dpy: !Display_ptr l
  , colormap: Colormap, colors: &(@[XColor][n]), ncolor: int n
  ) : void = "#atsctrb_XStoreColors"
// end of [XStoreColors]

(*
XcmsStoreColor (...)
XcmsStoreColors (...)
*)

fun XStoreNamedColor {l:anz} (
    dpy: !Display_ptr l
  , colormap: Colormap, color_name: string, pixel: ulint, flags: int
  ) : void = "#atsctrb_XStoreNamedColor"
// end of [XStoreNamedColor]

fun XQueryColor {l:anz} (
    dpy: !Display_ptr l
    , colormap: Colormap, def_in_out: &XColor >> XColor
  ) : void = "#atsctrb_XQueryColor"
// end of [XQueryColor]

fun XQueryColors {l:anz} {n:nat} (
    dpy: !Display_ptr l
  , colormap: Colormap, defs_in_out: &(@[XColor][n]), ncolor: int n
  ) : void = "#atsctrb_XQueryColors"
// end of [XQueryColors]

(*
fun XcmsQueryColor (...)
fun XcmsQueryColors (...)
*)

(* ****** ****** *)

// 6.8: Color Conversion Context Functions

(* ****** ****** *)

// 6.9: Converting Between Color Spaces

(* ****** ****** *)

// 6.10: Callback functions

(* ****** ****** *)

// 6.11: Gamut querying functions

(* ****** ****** *)

// 6.12: Color management extensions

(* ****** ****** *)

//
// Chapter 7: Graphics Context Functions
//

(* ****** ****** *)

// 7.1: Manipulating Graphics Context/State

macdef GCFunction = $extval (lint, "GCFunction")
macdef GCPlaneMask = $extval (lint, "GCPlaneMask")
macdef GCForeground = $extval (lint, "GCForeground")
macdef GCBackground = $extval (lint, "GCBackground")
macdef GCLineWidth = $extval (lint, "GCLineWidth")
macdef GCLineStyle = $extval (lint, "GCLineStyle")
macdef GCCapStyle = $extval (lint, "GCCapStyle")
macdef GCJoinStyle = $extval (lint, "GCJoinStyle")
macdef GCFillStyle = $extval (lint, "GCFillStyle")
macdef GCFillRule = $extval (lint, "GCFillRule")
macdef GCTile = $extval (lint, "GCTile")
macdef GCStipple = $extval (lint, "GCStipple")
macdef GCTileStipXOrigin = $extval (lint, "GCTileStipXOrigin")
macdef GCTileStipYOrigin = $extval (lint, "GCTileStipYOrigin")
macdef GCFont = $extval (lint, "GCFont")
macdef GCSubWindowMode = $extval (lint, "GCSubWindowMode")
macdef GCGraphicsExposures = $extval (lint, "GCGraphicsExposures")
macdef GCClipXOrigin = $extval (lint, "GCClipXOrigin")
macdef GCClipYOrigin = $extval (lint, "GCClipYOrigin")
macdef GCClipMask = $extval (lint, "GCClipMask")
macdef GCDashOffset = $extval (lint, "GCDashOffset")
macdef GCDashList = $extval (lint, "GCDashList")
macdef GCArcMode = $extval (lint, "GCArcMode")

typedef XGCValues =
  $extype_struct "XGCValues" of {
  function= int
, plane_mask= ulint
, foreground= ulint
, background= ulint
, line_width= int
, line_style= int
, cap_style= int
, join_style= int
, fill_style= int
, arc_mode= int
, tile= Pixmap
, stipple= Pixmap
, ts_x_origin = int
, ts_y_origin = int
, font= Font
, subwindow_mode= int
, graphics_exposures= XBool
, clip_x_origin= int
, clip_y_origin= int
, clip_mask= Pixmap
, dash_offset= int
, dashes= char
} // end of [XGCValues]

fun XCreateGC {l:anz} ( // [values] can be uninitialized ...
    dpy: !Display_ptr l, drw: Drawable, mask: ulint, values: &XGCValues?
  ) : [l:addr] GCptr l
  = "#atsctrb_XCreateGC"
// end of [XCreateGC]

fun XCopyGC {l1:addr} {l2,l3:addr}
  (dpy: !Display_ptr l1, src: !GCptr l2, dst: !GCptr l3, mask: ulint): void
  = "#atsctrb_XCopyGC"
// end of [XCopyGC]

fun XChangeGC {l1:anz} {l2:addr}
  (dpy: !Display_ptr l1, gc: !GCptr l2, mask: ulint, values: &XGCValues): void
  = "#atsctrb_XChangeGC"
// end of [XChangeGC]

fun XGetGCValues {l1:anz} {l2:addr} (
    dpy: !Display_ptr l1, gc: !GCptr l2, mask: ulint, values: &XGCValues? >> XGCValues
  ) : void = "#atsctrb_XGetGCValues"
// end of [XGetGCValues]

fun XFreeGC {l1:anz} {l2:addr} (dpy: !Display_ptr l1, gc: GCptr l2): void
  = "#atsctrb_XFreeGC"
// end of [XFreeGC]

fun XFlushGC {l1:anz} {l2:addr} (dpy: !Display_ptr l1, gc: !GCptr l2): void
  = "#atsctrb_XFlushGC"
// end of [XFlushGC]

(* ****** ****** *)

// 7.2: Using GC convenience routines

fun XSetForeground {l1:anz} {l2:addr}
  (dpy: !Display_ptr l1, gc: !GCptr l2, foreground: ulint): void
  = "#atsctrb_XSetForeground"
// end of [XSetForeground]

fun XSetBackground {l1:anz} {l2:addr}
  (dpy: !Display_ptr l1, gc: !GCptr l2, background: ulint): void
  = "#atsctrb_XSetBackground"
// end of [XSetBackground]                                    

fun XSetFunction {l1:anz} {l2:addr}
  (dpy: !Display_ptr l1, gc: !GCptr l2, _function: int): void
  = "#atsctrb_XSetFunction"
// end of [XSetFunction]                                    

fun XSetPlaneMask {l1:anz} {l2:addr}
  (dpy: !Display_ptr l1, gc: !GCptr l2, plane_mask: ulint): void
  = "#atsctrb_XSetPlaneMask"
// end of [XSetPlaneMask]                                    

fun XSetFont {l1:anz} {l2:addr}
  (dpy: !Display_ptr l1, gc: !GCptr l2, font: Font): void
  = "#atsctrb_XSetFont"
// end of [XSetFont]

fun XSetLineAttributes
  {l1:anz} {l2:addr} (
    dpy: !Display_ptr l1, gc: !GCptr l2
  , line_width: uint, line_style: int, cap_style: int, join_style: int
  ) : void
  = "#atsctrb_XSetLineAttributes"
// end of [XSetLineAttributes]

fun XSetDashes
  {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1, gc: !GCptr l2
  , dash_offset: int, dash_list: &(@[char][n]), n: int n
  ) : void
  = "#atsctrb_XSetDashes"
// end of [XSetDashes]

(* ****** ****** *)

//
// Chapter 8: Graphics Functions
//

(* ****** ****** *)

// 8.1: Clearing Areas

fun XClearArea {l:anz} (
    dsp: !Display_ptr l
  , win: Window
  , x: int, y: int
  , width: uint, height: uint
  , exposures: XBool
  ) : void
  = "#atsctrb_XClearArea"

fun XClearWindow {l:anz} (dsp: !Display_ptr l, win: Window) : void
  = "#atsctrb_XClearWindow"
// end of [XClearWindow]

(* ****** ****** *)

// 8.2: Copying Areas

fun XCopyArea
  {l1:anz} {l2:addr} (
    dpy: !Display_ptr l1
  , src: Drawable, dst: Drawable
  , gc: !GCptr l2
  , x_src: int, y_src: int
  , width: uint, height: uint
  , x_dst: int, y_dst: int
  ) : void
  = "#atsctrb_XCopyArea"

fun XCopyPlane
  {l1:anz} {l2:addr} (
    dpy: !Display_ptr l1
  , src: Drawable, dst: Drawable
  , gc: !GCptr l2
  , x_src: int, y_src: int
  , width: uint, height: uint
  , x_dst: int, y_dst: int
  , plane: ulint // set exactly one-bit to 1
  ) : void
  = "#atsctrb_XCopyPlane"

(* ****** ****** *)

// 8.3: Drawing Points, Lines, Rectangles and Arcs

typedef XSegment =
  $extype_struct "XSegment" of {
  x1= sint, y1= sint, x2= sint, y2= sint
} // end of [XSegment]

typedef XPoint =
  $extype_struct "XPoint" of { x= sint, y= sint }
// end of [XPoint]

typedef XRectangle =
  $extype_struct "XRectangle" of {
  x= sint, y= sint, width= usint, height= usint
} // end of [XRectangle]

typedef XArc =
  $extype_struct "XArc" of {
  x= sint, y= sint
, width= usint, height= usint
, angle1= sint, angle2= sint // uint: 1/64 degree
} // end of [XArc]

(* ****** ****** *)

// 8.3.1: Drawing Single and Multiple Points

fun XDrawPoint {l1:anz} {l2:addr} (
    dpy: !Display_ptr l1, drw: Drawable, gc: !GCptr l2, x: int, y: int
  ) : void = "#atsctrb_XDrawPoint"
// end of [XDrawPoint]

fun XDrawPoints {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, points: &(@[XPoint][n]), n: int n, mode: int
  ) : void = "#atsctrb_XDrawPoints"
// end of [XDrawPoints]

(* ****** ****** *)

// 8.3.2: Drawing Single and Multiple Lines

fun XDrawLine {l1:anz} {l2:addr} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, x1: int, y1: int, x2: int, y2: int
  ) : void = "#atsctrb_XDrawLine"
// end of [XDrawLine]

fun XDrawLines {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, points: &(@[XPoint][n]), n: int n, mode: int
  ) : void = "#atsctrb_XDrawLines"
// end of [XDrawLines]

fun XDrawSegments {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, segments: &(@[XSegment][n]), n: int n
  ) : void = "#atsctrb_XDrawSegments"
// end of [XDrawSegments]

(* ****** ****** *)

// 8.3.3: Drawing Single and Multiple Rectangles

fun XDrawRectangle {l1:anz} {l2:addr} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, x: int, y: int, width: uint, height: uint
  ) : void = "#atsctrb_XDrawRectangle"
// end of [XDrawRectangle]

fun XDrawRectangles {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, rectangles: &(@[XRectangle][n]), n: int n
  ) : void = "#atsctrb_XDrawRectangles"
// end of [XDrawRectangles]

(* ****** ****** *)

// 8.3.4: Drawing Single and Multiple Arcs

fun XDrawArc {l1:anz} {l2:addr} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2
  , x: int, y: int, width: uint, height: uint, angle1: int, angle2: int
  ) : void = "#atsctrb_XDrawArc"
// end of [XDrawArc]

fun XDrawArcs {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, arcs: &(@[XArc][n]), n: int n
  ) : void = "#atsctrb_XDrawArcs"
// end of [XDrawArcs]

(* ****** ****** *)

// 8.4: Filling Areas

(* ****** ****** *)

// 8.4.1: Filling Single and Multiple Rectangles

fun XFillRectangle {l1:anz} {l2:addr} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, x: int, y: int, width: uint, height: uint
  ) : void = "#atsctrb_XFillRectangle"
// end of [XFillRectangle]

fun XFillRectangles {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, rectangles: &(@[XRectangle][n]), n: int n
  ) : void = "#atsctrb_XFillRectangles"
// end of [XFillRectangles]

(* ****** ****** *)

// 8.4.2: Filling a Single Polygon

fun XFillPolygon {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, points: &(@[XPoint][n]), n: int n
  , shape: int, mode: int
  ) : void = "#atsctrb_XFillPolygon"
// end of [XFillPolygon]

(* ****** ****** *)

// 8.4.3: Filling Single and Multiple Arcs

fun XFillArc {l1:anz} {l2:addr} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2
  , x: int, y: int, width: uint, height: uint, angle1: int, angle2: int
  ) : void = "#atsctrb_XFillArc"
// end of [XFillArc]

fun XFillArcs {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable, gc: !GCptr l2, arcs: &(@[XArc][n]), n: int n
  ) : void = "#atsctrb_XFillArcs"
// end of [XFillArcs]

(* ****** ****** *)

// 8.5: Font Metrics

typedef XCharStruct =
  $extype_struct "XCharStruct" of {
  lbearing= sint, rbearing= sint
, width= sint, ascent= sint, descent= sint
, attributes= usint
} // end of [XCharStruct]

typedef XFontProp =
  $extype_struct "XFontProp" of { name= Atom, card32= ulint }
// end of [XFontProp]

typedef XChar2b =
  $extype_struct "XChar2b" of { byte1= uchar, byte2= uchar }
// end of [XChar2b]

typedef XFontStruct = $extype_struct "XFontStruct" of {
  XExtData= ptr
, fid= Font
, direction= uint
, min_char_or_byte2= uint
, max_char_or_byte2= uint
, min_byte1= uint
, max_byte1= uint
, all_chars_exist= XBool
, default_char= uint
// , n_properties= int n
// , properties= ptr l_properties // @[XFontProp][n] @ l_properties
, min_bounds= XCharStruct
, max_bounds= XCharStruct
// , per_char= ptr // XCharStruct*
, ascent= int
, descent= int
} // end of [XFontStruct]

(* ****** ****** *)

// 8.5.1: Loading and Freeing Fonts

absview XFreeFont_v (l:addr)
prfun XFreeFont_v_unnull (pf: XFreeFont_v null): void

fun XLoadFont {l:anz}
  (dpy: !Display_ptr l, name: string): Font = "#atsctrb_XLoadFont"
// end of [XLoadFont]

fun XQueryFont {l:anz}
  (dpy: !Display_ptr l, font_id: XID)
  : [l:addr] (XFreeFont_v l, ptropt_v (XFontStruct, l) | ptr l)
  = "#atsctrb_XQueryFont"
// end of [XQueryFont]

fun XLoadQueryFont {l:anz}
  (dpy: !Display_ptr l, name: string)
  : [l:addr] (XFreeFont_v l, ptropt_v (XFontStruct, l) | ptr l)
  = "#atsctrb_XLoadQueryFont"
// end of [XLoadQueryFont]

fun XFreeFont {l1:anz} {l2:addr} (
    pf1: XFreeFont_v l2, pf2: XFontStruct @ l2
  | dpy: !Display_ptr l1, p_font_struct: ptr l2
  ) : void
  = "#atsctrb_XFreeFont"
// end of [XFreeFont]
            
(* ****** ****** *)

// 8.5.3: Computing Character String Sizes

fun XTextWidth {n:nat}
  (ftinfo: &XFontStruct, str: string n, nstr: int n): int
  = "#atsctrb_XTextWidth"
// end of [XTextWidth]

fun XTextWidth16 {n:nat}
  (ftinfo: &XFontStruct, str: array (XChar2b, n), nstr: int n): int
  = "#atsctrb_XTextWidth16"
// end of [XTextWidth]

(* ****** ****** *)

// 8.6: Drawing Text

(* ****** ****** *)

// 8.6.2: Drawing Text Characters

fun XDrawString
  {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable
  , gc: !GCptr l2
  , x: int, y: int
  , str: string n
  , len: int n
  ) : void = "#atsctrb_XDrawString"
// end of [XDrawString]

fun XDrawString16
  {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable
  , gc: !GCptr l2
  , x: int, y: int
  , str: array (XChar2b, n)
  , len: int n
  ) : void = "#atsctrb_XDrawString16"
// end of [XDrawString16]

(* ****** ****** *)

// 8.6.2: Drawing Text Characters

fun XDrawString
  {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable
  , gc: !GCptr l2
  , x: int, y: int
  , str: string n
  , len: int n
  ) : void = "#atsctrb_XDrawString"
// end of [XDrawString]

fun XDrawString16
  {l1:anz} {l2:addr} {n:nat} (
    dpy: !Display_ptr l1
  , drw: Drawable
  , gc: !GCptr l2
  , x: int, y: int
  , str: array (XChar2b, n)
  , len: int n
  ) : void = "#atsctrb_XDrawString16"
// end of [XDrawString16]

(* ****** ****** *)

//
// Chapter 9: Window and Session Manager Functions
//

(* ****** ****** *)

// 9.1: Changing the parent of a window

fun XReparentWindow {l:anz}
  (dpy: !Display_ptr l, win: Window, parent: Window, x: int, y: int): void
  = "#atsctrb_XReparentWindow"
// end of [XReparentWindow]

(* ****** ****** *)

// 9.2: Controlling the Lifetime of a Window

fun XChangeSaveSet {l:anz}
  (dpy: !Display_ptr l, win: Window, mode: int): void
  = "#atsctrb_XChangeSaveSet"
// end of [atsctrb_XChangeSaveSet]

fun XAddSaveSet {l:anz}
  (dpy: !Display_ptr l, win: Window): void = "#atsctrb_XAddSaveSet"
// end of [XAddSaveSet]

fun XRemoveFromSaveSet {l:anz}
  (dpy: !Display_ptr l, win: Window): void = "#atsctrb_XRemoveFromSaveSet"
// end of [XRemoveFromSaveSet]

(* ****** ****** *)

// 9.3: Managing installed colormaps

fun XInstallColormap {l:anz}
  (dpy: !Display_ptr l, colormap: Colormap): void = "#atsctrb_XInstallColormap"
// end of [XInstallColormap]

fun XUninstallColormap {l:anz}
  (dpy: !Display_ptr l, colormap: Colormap): void = "#atsctrb_XUninstallColormap"
// end of [XUninstallColormap]

fun XListInstalledColormaps {l:anz} (
    dpy: !Display_ptr l, win: Window, nmap: &int? >> int n
  ) : #[la:addr;n:nat] (
    XFree_v (Colormap, n, la), @[Colormap][n] @ la | ptr la
  ) = "#atsctrb_XListInstalledColormaps"
// end of [XListInstalledColormaps]

(* ****** ****** *)

// 9.4: Setting and Retrieving the Fond Search Path

(* ****** ****** *)

// 9.5: Server Grabbing

fun XGrabServer {l:anz}
  (dpy: !Display_ptr l): void = "#atsctrb_XGrabServer"
// end of [XGrabServer]

fun XUngrabServer {l:anz}
  (dpy: !Display_ptr l): void = "#atsctrb_XUngrabServer"
// end of [XUngrabServer]

(* ****** ****** *)

// 9.6: Killing Clients

fun XKillClient {l:anz}
  (dpy: !Display_ptr l, resource: XID): void = "#atsctrb_XKillClient"
// end of [XKillClient]

(* ****** ****** *)

// 9.7: Screen Saver Control

fun XSetScreenSaver {l:anz} (
    dpy: !Display_ptr l
  , timeout: int, interval: int, prefer_blanking: int, allow_exposures: int
  ) : void = "#atsctrb_XSetScreenSaver"
// end of [XSetScreenSaver]

fun XForceScreenSaver
  {l:anz} (dpy: !Display_ptr l, mode: int): void = "#atsctrb_XForceScreenSaver"
// end of [XForceScreenSaver]

fun XActivateScreenSaver
  {l:anz} (dpy: !Display_ptr l): void = "#atsctrb_XActivateScreenSaver"
// end of [XActivateScreenSaver]

fun XResetScreenSaver
  {l:anz} (dpy: !Display_ptr l): void = "#atsctrb_XResetScreenSaver"
// end of [XResetScreenSaver]

fun XGetScreenSaver {l:anz} (
    dpy: !Display_ptr l
  , timeout: &int? >> int
  , interval: &int? >> int
  , prefer_blanking: &int? >> int
  , allow_exposures: &int? >> int
  ) : void = "#atsctrb_XGetScreenSaver"
// end of [XGetScreenSaver]

(* ****** ****** *)

// 9.8: Controlling Host Access

(* ****** ****** *)

// 9.8.1: Adding, Getting or Removing Hosts

typedef XHostAddress = $extype_struct "XHostAddress" of {
  family= int
, length= int
, address= string
} // end of [XHostAddress]

fun XAddHost {l:anz}
  (dpy: !Display_ptr l, host: &XHostAddress): void = "#atsctrb_XAddHost"
// end of [XAddHost]

fun XAddHosts {l:anz} {n:nat}
  (dpy: !Display_ptr l, hosts: &(@[XHostAddress][n]), n: int n): void
  = "#atsctrb_XAddHosts"
// end of [XAddHosts]

fun XListHosts {l:anz} (
    dpy: !Display_ptr l, nhost: &int? >> int n, state: &XBool? >> XBool
  ) : #[la:addr;n:nat] (
    XFree_v (XHostAddress, n, la), @[XHostAddress][n] @ la | ptr la
  ) = "#atsctrb_XListHosts"
// end of [XListHosts]

fun XRemoveHost {l:anz}
  (dpy: !Display_ptr l, host: &XHostAddress): void
  = "#atsctrb_XRemoveHost"
// end of [XRemoveHost]

fun XRemoveHosts {l:anz} {n:nat}
  (dpy: !Display_ptr l, hosts: &(@[XHostAddress][n]), n: int n): void
  = "#atsctrb_XRemoveHosts"
// end of [XRemoveHosts]

(* ****** ****** *)

// 9.8.2: Changing, Enabling or Disabling Access Control

fun XSetAccessControl {l:anz}
  (dpy: !Display_ptr l, mode: int): void = "#atsctrb_XSetAccessControl"
// end of [XSetAccessControl]

fun XEnableAccessControl {l:anz}
  (dpy: !Display_ptr l): void = "#atsctrb_XEnableAccessControl"
// end of [XEnableAccessControl]

fun XDisableAccessControl {l:anz}
  (dpy: !Display_ptr l): void = "#atsctrb_XDisableAccessControl"
// end of [XDisableAccessControl]

(* ****** ****** *)

//
// Chapter 10: Events
//

(* ****** ****** *)

abst@ype XEvent_rest // unknown quantity

typedef XEvent =
  $extype_struct "XEvent" of {
  type= EventType_t // the type of the event
, _rest= XEvent_rest // this field is abstract and cannot be accessed
} // end of [XEvent]

propdef XEvent_castdn_t (a:t@ype) = {l:addr}
  (XEvent @ l) -<prf> (a @ l, a @ l -<lin,prf> XEvent @ l)
// end of [XEvent_castdn_t]

(* ****** ****** *)

// 10.2: Event Structures

typedef XAnyEvent = $extype_struct "XAnyEvent" of {
  type= EventType_t
, serial = ulint // # of last request processed by server
, send_event= XBool // true if this comes from a SendEvent request
/*
, display= Display_ptr0 // Display the event was read freom
*/
, window= Window
} // end of [XAnyEvent]

praxi XEvent_xany_castdn : XEvent_castdn_t (XAnyEvent)

(* ****** ****** *)

// 10.5: Keyboard and Pointer Events

(* ****** ****** *)

typedef XKeyEvent = $extype_struct "XKeyEvent" of {
  type= EventType_t
, serial= ulint
, send_event= XBool
/*
, display= Display_ptr0 // Display the event was read freom
*/
, window= Window
// individual section
, root= Window
, subwindow= Window
/*
, time= Time
*/
, x= int, y= int
, x_root= int, y_root= int
, state= uint
, keycode= uint
, same_screen= XBool  
} // end of [XKeyEvent]

praxi XEvent_xkey_castdn : XEvent_castdn_t (XKeyEvent)

//

typedef XKeyPressedEvent = XKeyEvent
typedef XKeyReleasedEvent = XKeyEvent

//

typedef XButtonEvent = $extype_struct "XButtonEvent" of {
  type= EventType_t
, serial= ulint
, send_event= XBool
/*
, display= Display_ptr0 // Display the event was read freom
*/
, window= Window
// individual section
, root= Window
, subwindow= Window
/*
, time= Time
*/
, x= int, y= int
, x_root= int, y_root= int
, state= uint
, button= uint
, same_screen= XBool
} // end of [XButtonEvent]

praxi XEvent_xbutton_castdn : XEvent_castdn_t (XButtonEvent)

//

typedef XMotionEvent = $extype_struct "XMotionEvent" of {
  type= EventType_t
, serial= ulint
, send_event= XBool
/*
, display= Display_ptr0 // Display the event was read freom
*/
, window= Window
// individual section
, root= Window
, subwindow= Window
/*
, time= Time
*/
, x= int, y= int
, x_root= int, y_root= int
, state= uint
, in_hint= char
, same_screen= XBool  
} // end of [XMotionEvent]

praxi XEvent_xmotion_castdn : XEvent_castdn_t (XMotionEvent)

(* ****** ****** *)

// 10.6: Window Entry/Exit Events

(* ****** ****** *)

// 10.7: Input Focus Events

(* ****** ****** *)

// 10.8: Key Map State Notification Events

(* ****** ****** *)

// 10.9: Exposure Events

typedef XExposeEvent = $extype_struct "XExposeEvent" of {
  type= EventType_t
, serial= ulint
, send_event= XBool
/*
, display= Display_ptr0 // Display the event was read freom
*/
, window= Window
// individual section
, x= int, y= int
, width= int, height= int
, count= int  
} // end of [XExposeEvent]

praxi XEvent_xexpose_castdn : XEvent_castdn_t (XExposeEvent)

(* ****** ****** *)

// 10.10: Window State Change Events

(* ****** ****** *)

// 10.10.1: CirculateNotify Events

typedef XCirculateEvent =
  $extype_struct "XCirculateEvent" of {
  type= EventType_t
, serial= ulint
, send_event= XBool
/*
, display= Display_ptr0 // Display the event was read freom
*/
// individual section
, event= Window
, window= Window
, place= int  
} // end of [XCirculateEvent]

praxi XEvent_xcirculate_castdn : XEvent_castdn_t (XCirculateEvent)

(* ****** ****** *)

//
// Chapter 11: Event Handling Functions
//

(* ****** ****** *)

// 11.1: selecting events

fun XSelectInput {l:anz}
  (dpy: !Display_ptr l, win: Window, eventmask: InputEventMask_t): void
  = "#atsctrb_XSelectInput"
// end of [XSelectInput]

(* ****** ****** *)

// 11.2: handling the output buffer

fun XFlush {l:anz} (dpy: !Display_ptr l): void
  = "#atsctrb_XFlush"
// end of [XFlush]

fun XSync {l:anz} (dpy: !Display_ptr l, discard: bool): void
  = "#atsctrb_XSync"
// end of [XSync]

(* ****** ****** *)

// 11.3: Event Queue Management

macdef QueuedAlready = $extval (int, "QueuedAlready")
macdef QueuedAfterReading = $extval (int, "QueuedAfterReading")
macdef QueuedAfterFlush = $extval (int, "QueuedAfterFlush")

fun XEventsQueued {l:anz} (dpy: Display_ptr l, mode: int): int
  = "#atsctrb_XEventsQueued"
// end of [XEventsQueued]

// this one is equivalent to XEventsQueued (QueuedAfterFlush)
fun XPending {l:anz} (dpy: Display_ptr l): int = "#atsctrb_XPending"

(* ****** ****** *)

// 11.4: manipulating the event queue

(* ****** ****** *)

// 11.4.1: returning the next event

fun XNextEvent {l:anz}
  (dpy: !Display_ptr l, event: &XEvent? >> XEvent): void = "#atsctrb_XNextEvent"
// end of [XNextEvent]

fun XPeekEvent {l:anz}
  (dpy: !Display_ptr l, event: &XEvent? >> XEvent): void = "#atsctrb_XPeekEvent"
// end of [XPeekEvent]

(* ****** ****** *)

//
// Chapter 14: Inter-client communication functions
//

// source: "X11/Xutil.h"

(* ****** ****** *)

// 14.1: Client to Window Manage Communication

typedef XTextProperty =
  $extype_struct "XTextProperty" of {
  value= ptr // property data
, encoding= Atom // type of property
, format= int // 8, 16, or 32
, nitems= ulint // number of items in value
} // end of [XTextProperty]

(* ****** ****** *)

abst@ype XICCEncodingStyle = $extype "XICCEncodingStyle"

macdef XStringStyle = $extval (XICCEncodingStyle, "XStringStyle")
macdef XCompoundTextStyle = $extval (XICCEncodingStyle, "XCompoundTextStyle")
macdef XTextStyle = $extval (XICCEncodingStyle, "XTextStyle")
macdef XStdICCTextStyle = $extval (XICCEncodingStyle, "XStdICCTextStyle")

(* ****** ****** *)

// 14.1.6: Setting and Reading the WM_HINTS Property

macdef InputHint = $extval (lint, "InputHint")
macdef StateHint = $extval (lint, "StateHint")
macdef IconPixmapHint = $extval (lint, "IconPixmapHint")
macdef IconWindowHint = $extval (lint, "IconWindowHint")
macdef IconPositionHint = $extval (lint, "IconPositionHint")
macdef IconMaskHint = $extval (lint, "IconMaskHint")
macdef WindowGroupHint = $extval (lint, "WindowGroupHint")
macdef AllHints = $extval (lint, "AllHints")
macdef XUrgencyHint = $extval (lint, "XUrgencyHint")

typedef XWMHints =
  $extype_struct "XWHints" of {
  flags= lint // marks which fields in this structure are defined
, input= XBool // does this application rely on the window manager to get keyword input?
, initial_state= int // see below
, icon_pixmap= Pixmap // pixmap to be used as icon
, icon_window= Window // window to be used as icon
, icon_x= int, icon_y= int // initial position of icon
, icon_mask= Pixmap // pixmap to be used as mask for icon_pixmap
, window_group= XID // id of related window group // may be extended in the future
} // end of [XWMHints]

fun XAllocWMHints ()
  : [l:addr] (XFree_v (XWMHints, l), ptropt_v (XWMHints?, l) | ptr l)
  = "#atsctrb_XAllocWMHints"
// end of [XAllocWMHints]

fun XSetWNHints {l:addr}
  (dpy: !Display_ptr l, win: Window, wmhints: &XWMHints): void
  = "#atsctrb_XSetWNHints"
// end of [XSetWNHints]

fun XGetWNHints {l:addr}
  (dpy: !Display_ptr l, win: Window)
  : [l:addr] (XFree_v (XWMHints, l), ptropt_v (XWMHints, l) | ptr l)
  = "#atsctrb_XGetWNHints"
// end of [XGetWNHints]

(* ****** ****** *)

// 14.1.7: Setting and Reading the WM_NORMAL Property

typedef XSizeHints_aspect =
  $extype_struct "XSizeHints_aspect" of { x= int, y= int }
// end of [XSizeHints_aspect]

macdef USPosition = $extval (lint, "USPosition")
macdef USSize = $extval (lint, "USSize")
macdef PPosition = $extval (lint, "PPosition")
macdef PSize = $extval (lint, "PSize")
macdef PMinSize = $extval (lint, "PMinSize")
macdef PMaxSize = $extval (lint, "PMaxSize")
macdef PResizeInc = $extval (lint, "PResizeInc")
macdef PAspect = $extval (lint, "PAspect")
macdef PBaseSize = $extval (lint, "PBaseSize")
macdef PWinGravity = $extval (lint, "PWinGravity")

typedef XSizeHints =
  $extype_struct "XSizeHints" of {
  flags= lint
, x= int, y= int
, width= int, height= int
, min_width= int, min_height= int
, max_width= int, max_height= int
, width_inc= int, height_inc= int
, min_aspect= XSizeHints_aspect, max_aspect= XSizeHints_aspect
, base_width= int, base_height= int
, win_gravity= int
} // end of [XSizeHints]

fun XAllocSizeHints ()
  : [l:addr] (XFree_v (XSizeHints, l), ptropt_v (XSizeHints?, l) | ptr l)
  = "#atsctrb_XAllocSizeHints"
// end of [XAllocSizeHints]

//

fun XSetWMNormalHints {l:anz}
  (dpy: !Display_ptr l, win: Window, hints: &XSizeHints): void
  = "#atsctrb_XSetWMNormalHints"
// end of [XSetWMNormalHints]

fun XGetWMNormalHints {l:anz} (
    dpy: !Display_ptr l, win: Window
  , hints: &XSizeHints? >> XSizeHints, supplied: &lint? >> lint
  ) : Status
  = "#atsctrb_XGetWMNormalHints"
// end of [XGetWMNormalHints]

//

fun XSetWMSizeHints {l:anz}
  (dpy: !Display_ptr l, win: Window, hints: &XSizeHints, property: Atom): void
  = "#atsctrb_XSetWMSizeHints"
// end of [XSetWMSizeHints]

fun XGetWMSizeHints {l:anz} (
    dpy: !Display_ptr l, win: Window
  , hints: &XSizeHints? >> XSizeHints, supplied: &lint? >> lint, property: Atom
  ) : Status
  = "#atsctrb_XGetWMSizeHints"
// end of [XGetWMSizeHints]

(* ****** ****** *)

// 14.1.8: Setting and Reading the WM_CLASS Property

typedef XClassHint = $extype_struct "XClassHint" of {
  res_name= string
, res_class= string
} // end of [XClassHint]

fun XAllocClassHint ()
  : [l:addr] (XFree_v (XClassHint, l), ptropt_v (XClassHint?, l) | ptr l)
  = "#atsctrb_XAllocClassHint"
// end of [XAllocClassHint]

fun XSetClassHint {l:anz}
  (dpy: !Display_ptr l, win: Window, class_hint: XClassHint): void
  = "#atsctrb_XSetClassHint"

fun XGetClassHint {l:anz}
  (dpy: !Display_ptr l, win: Window, class_hint: &XClassHint? >> XClassHint): Status
  = "#atsctrb_XGetClassHint"

(* ****** ****** *)

//
// Chapter 16: Application Unitility Functions
//

(* ****** ****** *)

// 16.9: Manipulating Bitmaps

fun XCreatePixmapFromBitmapData {l:anz} (
    dpy: !Display_ptr l
  , drw: Drawable, data: ptr(*chars*)
  , width: uint, height: uint, fg: ulint, bg: ulint, depth: uint
  ) : Pixmap
  = "#atsctrb_XCreatePixmapFromBitmapData"
// end of [XCreatePixmapFromBitmapData]

fun XCreateBitmapFromData {l:anz} (
    dpy: !Display_ptr l
  , drw: Drawable, data: ptr(*chars*), width: uint, height: uint
  ) : Pixmap
  = "#atsctrb_XCreateBitmapFromData"
// end of [XCreateBitmapFromData]

(* ****** ****** *)

// 16.10: Using the Context Manager

(* ****** ****** *)

(* end of [Xlib.sats] *)
