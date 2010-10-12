(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)  *)

(* ****** ****** *)
//
// HX: some convenience functions
//
(* ****** ****** *)

staload "libc/sys/SATS/socket.sats"
staload "libc/netinet/SATS/in.sats"

(* ****** ****** *)

fun sockaddr_in_init (
    sa: &sockaddr_in_struct? >> sockaddr_in_struct
  , af: sa_family_t, inp: in_addr_nbo_t, port: in_port_nbo_t
  ) :<> void = "atslib_sockaddr_ipv4_init"
// end of [sockaddr_in_init]

(* ****** ****** *)

fun connect_in_exn {fd:int} (
    pf: !socket_v (fd, init) >> socket_v (fd, conn)
  | fd: int fd, servaddr: &sockaddr_in_struct // len=sizeof(sockaddr_in_struct)
  ) : void
// end of [connect_in_exn]

(* ****** ****** *)

fun bind_in_exn {fd:int} (
    pf_sock: !socket_v (fd, init) >> socket_v (fd, bind)
  | fd: int fd, servaddr: &sockaddr_in_struct // len=sizeof(sockaddr_in_struct)
  ) : void
// end of [bind_in_exn]

(* ****** ****** *)

(* end of [socket_in.sats] *)
