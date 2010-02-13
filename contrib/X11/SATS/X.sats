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
// #include "contrib/X11/CATS/X.cats"
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

(* end of [X.sats] *)
