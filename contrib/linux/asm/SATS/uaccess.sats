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
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)
// Start Time: February, 2011
//
(* ****** ****** *)

%{#
#include "contrib/linux/CATS/asm/uaccess.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

fun copy_to_user {n:nat}
  {n1,n2:nat | n <= n1; n <= n2} (
  to: &bytes(n1), from: &bytes(n2), count: ulint (n)
) : [nleft:nat | nleft <= n] ulint (nleft)
  = "#atsctrb_linux_copy_to_user" // macro!

fun copy_from_user {n:nat}
  {n1,n2:nat | n <= n1; n <= n2} (
  to: &bytes(n1), from: &bytes(n2), count: ulint (n)
) : [nleft:nat | nleft <= n] ulint (nleft)
  = "#atsctrb_linux_copy_from_user" // macro!

(* ****** ****** *)

(* end of [asm.sats] *)
