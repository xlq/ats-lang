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
#include "contrib/Xlib/CATS/Xlib.cats"
%} // end of [{%#]

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

(* ****** ****** *)

fun XOpenDisplay (name: string): Display_ptr0 = "#atsctrb_XOpenDisplay"

fun Display_ptr_is_null {l:addr} (p_dpy: !Display_ptr l): bool (l == null)
  = "atspre_ptr_is_null" // defined in $ATSHOME/prelude/CATS/pointer.cats
fun Display_ptr_isnot_null {l:addr} (p_dpy: !Display_ptr l): bool (l <> null)
  = "atspre_ptr_isnot_null" // defined in $ATSHOME/prelude/CATS/pointer.cats

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

//
// Colormap is XID, which is unsigned long 
//
abst@ype Colormap = $extype "Colormap" // for colormap ids
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

//
// Window is XID
//
abst@ype Window = $extype "Window" // for window ids
fun XDefaultRootWindow {l:anz} (dpy: !Display_ptr l): Window
  = "#atsctrb_XDefaultRootWindow"

(* ****** ****** *)

fun XDefaultScreen {l:anz} (dpy: !Display_ptr l): int(*nscr*)
  = "#atsctrb_XDefaultScreen"

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
macdef <SBFirst = $extval (int, "MSBFirst")

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

fun XNoOp {l:anz} (dpy: Display_ptr l): void
  = "#atsctrb_XNoOp"

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

fun XCloseDisplay (dpy: Display_ptr1): void = "#atsctrb_XCloseDisplay"

abst@ype close_mode_t = int
macdef DestroyAll = $extval (close_mode_t, "DestroyAll")
macdef RetainPermanent = $extval (close_mode_t, "RetainPermanent")
macdef RetainTemporary = $extval (close_mode_t, "RetainTemporary")

// [XSetCloseDownMode] may generate a BadValue error
fun XSetCloseDownMode {l:anz} (dpy: Display_ptr l, mode: close_mode_t): void

(* ****** ****** *)

(* end of [Xlib.sats] *)
