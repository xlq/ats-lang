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

abst@ype sa_family_t = $extype "ats_int_type"
macdef AF_INET = $extval (sa_family_t, "AF_INET")
macdef AF_INET6 = $extval (sa_family_t, "AF_INET6")
macdef AF_UNIX = $extval (sa_family_t, "AF_UNIX")
macdef AF_UNSPEC = $extval (sa_family_t, "AF_UNSPEC")

(* ****** ****** *)

sta socklen_max: int // length of [sockaddr_storage]

(* ****** ****** *)

abst@ype socklen_t(n:int) = $extype "socklen_t"
castfn socklen_of_int {n:nat} (n: int n): socklen_t n

(* ****** ****** *)

abst@ype sockaddr_struct(n:int) // a generic type

(* ****** ****** *)

abst@ype sockaddr_storage_struct
  = $extype "ats_sockaddr_storage_type"
typedef sockaddr_max_struct = sockaddr_storage_struct

(* ****** ****** *)

macdef socklen_max =
  $extval (socklen_t(socklen_max), "atslib_socklen_max")
praxi sockaddr_max_trans {l:addr}
  (pf: !sockaddr_max_struct @ l >> sockaddr_struct(socklen_max) @ l): void
praxi sockaddr_trans_max {l:addr}
  (pf: !sockaddr_struct(socklen_max) @ l >> sockaddr_max_struct @ l): void

(* ****** ****** *)

(* end of [sockaddr.sats] *)
