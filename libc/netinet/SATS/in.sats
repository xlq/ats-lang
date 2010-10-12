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
#include "libc/netinet/CATS/in.cats"
%} // end of [%{#]

(* ****** ****** *)

staload SA = "libc/sys/SATS/sockaddr.sats"
typedef sa_family_t = $SA.sa_family_t
stadef socklen_t = $SA.socklen_t // int: length of a sockaddr
stadef sockaddr_struct = $SA.sockaddr_struct

(* ****** ****** *)

(*
macdef INET_ADDRSTRLEN = 16 // for IPv4 dotted-decimal string
macdef INET6_ADDRSTRLEN = 46 // for IPv6 hex string
*)

(* ****** ****** *)

(*
abst@ype in_port_t = $extype "in_port_t"
*)
abst@ype in_port_nbo_t = $extype "in_port_t"

fun in_port_nbo_of_int
  (n: int): in_port_nbo_t = "atslib_in_port_nbo_of_int"
// end of [in_port_nbo_of_int]

(* ****** ****** *)

(*
abst@ype in_addr_t = $extype "in_addr_t"
*)
abst@ype in_addr_hbo_t = $extype "in_addr_t"
abst@ype in_addr_nbo_t = $extype "in_addr_t"

(* ****** ****** *)

fun in_addr_nbo_of_hbo
  (n: in_addr_hbo_t): in_addr_nbo_t = "atslib_in_addr_nbo_of_hbo"
// end of [in_addr_nbo_of_hbo]

(* constant addresses in host-byte-order *)

// Address to accept any incoming messages: 0x00000000
macdef INADDR_ANY = $extval (in_addr_hbo_t, "INADDR_ANY")

// Address to send to all hosts: 0xffffffff
macdef INADDR_BROADCAST	= $extval (in_addr_hbo_t, "INADDR_BROADCAST")

// Address indicating an error return: 0xffffffff
macdef INADDR_NONE = $extval (in_addr_hbo_t, "INADDR_NONE")

// Network number for local host loopback
#define	IN_LOOPBACKNET 127

// Address to loopback in software to local host: 127.0.0.1
macdef INADDR_LOOPBACK = $extval (in_addr_hbo_t, "INADDR_LOOPBACK")

(* Defines for Multicast INADDR *)

// 0xe0000000 // 224.0.0.0
macdef INADDR_UNSPEC_GROUP = $extval (in_addr_hbo_t, "INADDR_UNSPEC_GROUP")

// 0xe0000001 // 224.0.0.1
macdef INADDR_ALLHOSTS_GROUP = $extval (in_addr_hbo_t, "INADDR_ALLHOSTS_GROUP")

// 0xe0000002 // 224.0.0.2
macdef INADDR_ALLRTRS_GROUP = $extval (in_addr_hbo_t, "INADDR_ALLRTRS_GROUP")

// 0xe00000ff // 224.0.0.255
macdef INADDR_MAX_LOCAL_GROUP = $extval (in_addr_hbo_t, "INADDR_MAX_LOCAL_GROUP")

(* ****** ****** *)

abst@ype uint16_t0ype_netbyteord = uint16_t0ype
typedef uint16_nbo = uint16_t0ype_netbyteord
fun htons (i: uint16_t0ype): uint16_t0ype_netbyteord = "atslib_htons"
fun ntohs (i: uint16_t0ype_netbyteord): uint16_t0ype = "atslib_ntohs"

abst@ype uint32_t0ype_netbyteord = uint32_t0ype
typedef uint32_nbo = uint32_t0ype_netbyteord
fun htonl (i: uint32_t0ype): uint32_t0ype_netbyteord = "atslib_htonl"
fun ntohl (i: uint32_t0ype_netbyteord): uint32_t0ype = "atslib_ntohl"

(* ****** ****** *)

typedef
in_addr_struct =
$extype_struct "ats_in_addr_type" of {
  s_addr= in_addr_nbo_t // IPv4 address of ulint
} // end of [in_addr_struct]

fun in_addr_struct_get_s_addr
  (inp: in_addr_struct): in_addr_nbo_t = "atslib_in_addr_struct_get_s_addr"
// end of [in_addr_struct_get_s_addr]

(* ****** ****** *)

typedef sockaddr_in_struct =
$extype_struct "ats_sockaddr_in_type" of {
  sin_family= sa_family_t
, sin_port= in_port_nbo_t // uint16
, sin_addr= in_addr_struct
} // end of [sockaddr_in_struct]
typedef sockaddr_in = sockaddr_in_struct

sta socklen_in : int // length of [sockaddr_in]
macdef socklen_in = $extval (socklen_t(socklen_in), "atslib_socklen_in")
praxi socklen_lte_in (): [socklen_in <= $SA.socklen_max] void
praxi sockaddr_in_trans {l:addr}
  (pf: !sockaddr_in_struct @ l >> sockaddr_struct(socklen_in) @ l): void
praxi sockaddr_trans_in {l:addr}
  (pf: !sockaddr_struct(socklen_in) @ l >> sockaddr_in_struct @ l): void

(* ****** ****** *)

typedef
in6_addr_struct =
$extype_struct
"ats_in_addr_type" of {
  s6_addr= @[uint8][16] // IPv6 address of 16 bytes
} // end of [in6_addr_struct]

(* ****** ****** *)

typedef sockaddr_in6_struct =
$extype_struct "ats_sockaddr_in6_type" of {
  sin6_family= sa_family_t
, sin6_port= in_port_nbo_t // uint16
, sin6_flowinfo= uint32
, sin6_addr= in6_addr_struct
, sin6_scope_id= uint32
} // end of [sockaddr_in_struct]
typedef sockaddr_in6 = sockaddr_in6_struct

sta socklen_in6 : int // length of [sockaddr_in6]
abst@ype sockaddr_in6_struct = $extype "ats_sockaddr_in6_type"
macdef socklen_in6 = $extval (socklen_t(socklen_in6), "atslib_socklen_in6")
//
praxi socklen_lte_in6 (): [socklen_in6 <= $SA.socklen_max] void
praxi sockaddr_in6_trans {l:addr}
  (pf: !sockaddr_in6_struct @ l >> sockaddr_struct(socklen_in6) @ l): void
praxi sockaddr_trans_in6 {l:addr}
  (pf: !sockaddr_struct(socklen_in6) @ l >> sockaddr_in6_struct @ l): void
//
(* ****** ****** *)

(* end of [in.sats] *)
