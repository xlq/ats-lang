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

symintr gtk_alignment_new

typedef
gtk_alignment_new_type (a:t@ype) = (
    a // xalign
  , a // yalign
  , a // xscale
  , a // yscale
  ) -<fun1> GtkAlignment_ptr1

fun gtk_alignment_new__type
  : gtk_alignment_new_type float = "#atsctrb_gtk_alignment_new"
overload gtk_alignment_new with gtk_alignment_new__type

fun gtk_alignment_new__gtype
  : gtk_alignment_new_type gfloat = "#atsctrb_gtk_alignment_new"
overload gtk_alignment_new with gtk_alignment_new__gtype

(* ****** ****** *)

(* end of [gtkalignment.sats] *)
