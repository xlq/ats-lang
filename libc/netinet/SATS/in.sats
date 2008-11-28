(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
 * Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)  *)

(* ****** ****** *)

%{#

#include "libc/netinet/CATS/in.cats"

%}

(* ****** ****** *)

abst@ype address_family_t = $extype "ats_int_type"

macdef AF_INET = $extval (address_family_t, "AF_INET")
macdef AF_INET6 = $extval (address_family_t, "AF_INET6")
macdef AF_UNIX = $extval (address_family_t, "AF_UNIX")
macdef AF_UNSPEC = $extval (address_family_t, "AF_UNSPEC")

(* ****** ****** *)

#define INET_ADDRSTRLEN 16 // for IPv4 dotted-decimal string
#define INET6_ADDRSTRLEN 46 // for IPv6 hex string

(* ****** ****** *)

abst@ype in_port_nbo_t = $extype "in_port_t"

fun in_port_nbo_of_int (n: int): in_port_nbo_t
  = "atslib_in_port_nbo_of_int"

(* ****** ****** *)

(*

[struct in_addr] and  [in_addr_t] are really the same:
struct in_addr { in_addr_t s_addr; }; // defined in [netinet/in.h]

*)

abst@ype in_addr_hbo_t = $extype "in_addr_t"
abst@ype in_addr_nbo_t = $extype "in_addr_t"

abst@ype in_addr_struct_t = $extype "in_addr_struct_t"

(* ****** ****** *)

fun in_addr_nbo_of_hbo (n: in_addr_hbo_t): in_addr_nbo_t
  = "atslib_in_addr_nbo_of_hbo"

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

fun in_addr_struct_s_addr_get (inp: in_addr_struct_t): in_addr_nbo_t
  = "atslib_in_addr_struct_s_addr_get"

(* ****** ****** *)

abst@ype uint16_t0ype_netbyteord = uint16_t0ype
abst@ype uint32_t0ype_netbyteord = uint32_t0ype

fun htons (i: uint16_t0ype): uint16_t0ype_netbyteord = "atslib_htons"
fun htonl (i: uint32_t0ype): uint32_t0ype_netbyteord = "atslib_htonl"

fun ntohs (i: uint16_t0ype_netbyteord): uint16_t0ype = "atslib_ntohs"
fun ntohl (i: uint32_t0ype_netbyteord): uint32_t0ype = "atslib_ntohl"

(* ****** ****** *)

(* end of [in.sats] *)
