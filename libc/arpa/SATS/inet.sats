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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)  *)

(* ****** ****** *)

%{#
#include "libc/arpa/CATS/inet.cats"
%} // end of [%{#]

(* ****** ****** *)

staload "libc/netinet/SATS/in.sats"

(* ****** ****** *)

fun inet_aton_exn
  (cp: string, inp: &in_addr_struct_t? >> in_addr_struct_t) :<!exn> void
  = "atslib_inet_aton_exn"
// end of [inet_aton_exn]

(* ****** ****** *)

//
// HX: this function is not reentrant
//
fun inet_ntoa (inp: in_addr_struct_t):<!ref> string = "#atslib_inet_ntoa"

(* ****** ****** *)

fun inet_pton_exn (
    af: address_family_t, cp: string, inp: &in_addr_struct_t? >> in_addr_struct_t
  ) :<!exn> void = "atslib_inet_pton_exn"
// end of [inet_pton_exn]

(* ****** ****** *)

(* end of [inet.sats] *)
