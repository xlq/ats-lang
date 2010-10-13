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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "libc/CATS/netdb.cats"
%} // end of [%{#]

(* ****** ****** *)

staload SA = "libc/sys/SATS/sockaddr.sats"
typedef sa_family_t = $SA.sa_family_t
stadef socklen_t = $SA.socklen_t
stadef sockaddr = $SA.sockaddr_struct
staload SOCKET = "libc/sys/SATS/socket.sats"
typedef socktype_t = $SOCKET.socktype_t
typedef sockprot_t = $SOCKET.sockprot_t

staload IN = "libc/netinet/SATS/in.sats"
typedef sockaddr_in = $IN.sockaddr_in_struct
staload UN = "libc/sys/SATS/un.sats"
typedef sockaddr_un = $UN.sockaddr_un_struct

(* ****** ****** *)

abst@ype ai_flag_t = uint
//
macdef AI_NONE = $extval (ai_flag_t, "0x0")
//
macdef AI_ALL = $extval (ai_flag_t, "AI_ALL")
macdef AI_ADDRCONFIG = $extval (ai_flag_t, "AI_ADDRCONFIG")
macdef AI_CANNONNAME = $extval (ai_flag_t, "AI_CANNONNAME")
macdef AI_NUMERICHOST = $extval (ai_flag_t, "AI_NUMERICHOST")
macdef AI_NUMERICSERV = $extval (ai_flag_t, "AI_NUMERICSERV")
macdef AI_PASSIVE = $extval (ai_flag_t, "AI_PASSIVE")
macdef AI_V4MAPPED = $extval (ai_flag_t, "AI_V4MAPPED")
//
fun lor_ai_flag_ai_flag
  (x1: ai_flag_t, x2: ai_flag_t): ai_flag_t = "atspre_lor_uint_uint"
overload lor with lor_ai_flag_ai_flag

(* ****** ****** *)

typedef
addrinfo_struct (n:int) =
$extype_struct "ats_addrinfo_type" of {
  ai_flags= ai_flag_t
, ai_family= sa_family_t
, ai_socktype= socktype_t
, ai_protocol= sockprot_t
, ai_addrlen=socklen_t(n)
// , ai_addr= ptr // sockaddr*
// , ai_canonname= string // char*
// , ai_next= ptr // struct addrinfo* 
} // end of [addrinfo_struct]
stadef addrinfo = addrinfo_struct
absviewtype addrinfoptr (l:addr) = ptr
viewtypedef addrinfoptr = [l:addr] addrinfoptr(l)

fun addrinfoptr_is_null
  {l:addr} (x: !addrinfoptr l): bool (l==null) = "atspre_ptr_is_null"
fun addrinfoptr_isnot_null
  {l:addr} (x: !addrinfoptr l): bool (l > null) = "atspre_ptr_isnot_null"

fun addrinfoptr_get_next
  {l:agz} (x: !addrinfoptr l)
  :<> [l1:addr] (minus (addrinfoptr l, addrinfoptr l1) |  addrinfoptr l1)
  = "#atslib_addrinfoptr_get_next"
// end of [addrinfoptr_get_next]

fun addrinfoptr_get_canonname {l:agz}
  (x: !addrinfoptr l):<> [l1:addr] (minus (addrinfoptr l, strptr l1) |  strptr l1)
  = "#atslib_addrinfoptr_get_canonname"
// end of [addrinfoptr_get_cannonname]

fun addrinfoptr_get_family
  {l:agz} (x: !addrinfoptr l):<> sa_family_t = "#atslib_addrinfoptr_get_family"
// end of [addrinfoptr_get_family]
fun addrinfoptr_get_socktype
  {l:agz} (x: !addrinfoptr l):<> socktype_t = "#atslib_addrinfoptr_get_socktype"
// end of [addrinfoptr_get_socktype]
fun addrinfoptr_get_protocol
  {l:agz} (x: !addrinfoptr l):<> sockprot_t = "#atslib_addrinfoptr_get_protocol"
// end of [addrinfoptr_get_protocol]

(* ****** ****** *)

fun addrinfoptr_get_addr_in {l:agz} (x: !addrinfoptr l)
  :<> [l1:addr] (sockaddr_in @ l1, minus (addrinfoptr l, sockaddr_in @ l1) |  ptr l1)
  = "#atslib_addrinfoptr_get_addr"
// end of [addrinfoptr_get_addr_in]

fun addrinfoptr_get_addr_un {l:agz} (x: !addrinfoptr l)
  :<> [l1:addr] (sockaddr_un @ l1, minus (addrinfoptr l, sockaddr_un @ l1) |  ptr l1)
  = "#atslib_addrinfoptr_get_addr"
// end of [addrinfoptr_get_addr_un]

(* ****** ****** *)

fun getaddrinfo (
    nodename: string
  , portname: string
  , hint: &addrinfo(0)
  , infop: &addrinfoptr? >> opt (addrinfoptr, i == 0)
  ) : #[i:int | i <= 0] int (i) // HX: error codes are negative
  = "#atslib_getaddrinfo"
// end of [getaddrinfo]

(* ****** ****** *)

fun gai_strerror
  (code: int): [l:agz] (strptr l -<lin,prf> void | strptr l)
  = "#atslib_gai_strerror"
// end of [gai_strerror]

(* ****** ****** *)

fun freeaddrinfo (infop: addrinfoptr): void = "#atslib_freeaddrinfo"

(* ****** ****** *)

(* end of [netdb.sats] *)
