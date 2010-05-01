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

typedef GdkColor =
  $extype_struct "GdkColor" of {
  pixel= guint32, red= guint16, green= guint16, blue= guint16
} // end of [GdkColor]

(* ****** ****** *)

typedef GdkPoint =
  $extype_struct "GdkPoint" of { x= gint, y= gint }
// end of [GdkPoint]

(* ****** ****** *)

typedef GdkRectangle =
  $extype_struct "GdkRectangle" of {
  x= gint
, y= gint
, width= gint
, height= gint
} // end of [GdkRectangle]

(* ****** ****** *)

typedef GdkSpan =
  $extype_struct "GdkSpan" of {
  x= gint, y= gint, width= gint(*number of pixels in a span*)
} // end of [GdkSpan]

(* ****** ****** *)

abst@ype GdkEventType = $extype "GdkEventType"
abst@ype GdkEventMask = $extype "GdkEventMask"
abst@ype GdkVisibilityState = $extype "GdkVisibilityState"
abst@ype GdkWindowState = $extype "GdkWindowState"

(* ****** ****** *)

(* end of [gdktypes.sats] *)
