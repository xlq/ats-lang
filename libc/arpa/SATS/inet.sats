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

fun inet_aton_err (
  cp: string
, inp: &in_addr_struct? >> opt (in_addr_struct, b)
) : #[b:bool] bool b = "atslib_inet_aton_err"
// end of [inet_aton_err]

fun inet_aton_exn (
  cp: string, inp: &in_addr_struct? >> in_addr_struct
) :<!exn> void = "atslib_inet_aton_exn"
// end of [inet_aton_exn]

(* ****** ****** *)
//
// HX: note that this one cannot tell
// -1 from 255.255.255.255 (a valid address)
//
fun inet_addr
  (cp: string): in_addr_nbo_t = "#atslib_inet_addr"
fun inet_network
  (cp: string): in_addr_hbo_t = "#atslib_inet_network"

(* ****** ****** *)

fun inet_makeaddr
  (net: int, host: int): in_addr_struct = "#atslib_inet_makeaddr"
// end of [inet_makeaddr]

(* ****** ****** *)

//
// HX: this function is not reentrant
//
fun inet_ntoa
  (inp: in_addr_struct)
  :<!ref> [l:agz] (strptr l -<lin,prf> void | strptr l)
  = "#atslib_inet_ntoa"
// end of [inet_ntoa]

(* ****** ****** *)

fun inet_lnaof
  (addr: in_addr_struct): in_addr_hbo_t = "#atslib_inet_lnaof"
// end of [inet_lnaof]

fun inet_netof
  (addr: in_addr_struct): in_addr_hbo_t = "#atslib_inet_netof"
// end of [inet_netof]

(* ****** ****** *)

fun inet_pton_err (
    af: address_family_t, cp: string
  , inp: &in_addr_struct? >> opt (in_addr_struct, i > 0)
  ) : #[i:int] int (i) = "#atslib_inet_pton_err"
// end of [inet_pton_err]

fun inet_pton_exn (
    af: address_family_t, cp: string, inp: &in_addr_struct? >> in_addr_struct
  ) :<!exn> void = "atslib_inet_pton_exn"
// end of [inet_pton_exn]

(* ****** ****** *)

(* end of [inet.sats] *)
