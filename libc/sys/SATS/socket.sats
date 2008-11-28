(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
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

#include "libc/sys/CATS/socket.cats"

%}

(* ****** ****** *)

staload "libc/netinet/SATS/in.sats"

(* ****** ****** *)

abst@ype socket_type_t = $extype "ats_int_type"

macdef SOCK_DGRAM = $extval (socket_type_t, "SOCK_DGRAM")
macdef SOCK_RAW = $extval (socket_type_t, "SOCK_RAW")
macdef SOCK_SEQPACKET = $extval (socket_type_t, "SOCK_SEQPACKET")
macdef SOCK_STREAM = $extval (socket_type_t, "SOCK_STREAM")

abst@ype socket_protocol_t = $extype "ats_int_type"

(* ****** ****** *)

abst@ype socklen_t = $extype "socklen_t"
abst@ype sockaddr_in_struct_t = $extype "struct sockaddr_in"

(* ****** ****** *)

// client: init -> connect
// server: init -> bind -> listen -> accept
datasort status = init | bind | listen | conn

absview socket_v (int, status)

dataview socket_opt_v (int) = 
  | socket_none (~1)
  | {fd:nat} socket_some (fd) of socket_v (fd, init)

fun socket_family_type_err
  (af: address_family_t, t: socket_type_t): [fd:int] (socket_opt_v fd | int fd)
  = "atslib_socket_family_type_err"

fun socket_family_type_exn
  (af: address_family_t, t: socket_type_t): [fd:int] (socket_v (fd, init) | int fd)
  = "atslib_socket_family_type_exn"

(* ****** ****** *)

fun sockaddr_ipv4_init {l:addr} (
    sa: &sockaddr_in_struct_t? >> sockaddr_in_struct_t
  , af: address_family_t, inp: in_addr_nbo_t, port: in_port_nbo_t
  ) :<> void
  = "atslib_sockaddr_ipv4_init"

(* ****** ****** *)

dataview connect_v (fd: int, int) =
  | connect_fail (fd, ~1) of socket_v (fd, init)
  | connect_succ (fd,  0) of socket_v (fd, conn)

fun connect_ipv4_err {fd:int} (
    pf: socket_v (fd, init) | sockfd: int fd, servaddr: &sockaddr_in_struct_t
  ) : [i:int] (connect_v (fd, i) | int i)
  = "atslib_connect_ipv4_err"

fun connect_ipv4_exn {fd:int} (
    pf: !socket_v (fd, init) >> socket_v (fd, conn)
  | sockfd: int fd, servaddr: &sockaddr_in_struct_t
  ) : void
  = "atslib_connect_ipv4_exn"

(* ****** ****** *)

dataview bind_v (fd:int, int) = 
  | bind_fail (fd, ~1) of socket_v (fd, init)
  | bind_succ (fd,  0) of socket_v (fd, bind)

fun bind_ipv4_err {fd:int}
  (pf: socket_v (fd, init) | sockfd: int fd, servaddr: &sockaddr_in_struct_t)
  : [i:int] (bind_v (fd, i) | int i)
  = "atslib_bind_ipv4_err"

fun bind_ipv4_exn {fd:int} (
    pf: !socket_v (fd, init) >> socket_v (fd, bind)
  | sockfd: int fd, servaddr: &sockaddr_in_struct_t
  ) : void
  = "atslib_bind_ipv4_exn"

(* ****** ****** *)

dataview listen_v (fd: int, int) = 
  | listen_fail (fd, ~1) of socket_v (fd, bind) 
  | listen_succ (fd,  0) of socket_v (fd, listen)

fun listen_err {fd:int}
  (pf: socket_v (fd, bind) | sockfd: int fd, backlog: Pos)
  : [i:int] (listen_v (fd, i) | int i)
  = "atslib_listen_err"

fun listen_exn {fd:int}
  (pf: !socket_v (fd, bind) >> socket_v (fd, listen) |
   sockfd: int fd, backlog: Pos): void
  = "atslib_listen_exn"

(* ****** ****** *)

dataview accept_v (int) = 
  | accept_fail (~1)
  | {fd:nat} accept_succ (fd) of socket_v (fd, conn)

fun accept_null_err {fd_s:int}
  (pf: !socket_v (fd_s, listen) | sockfd: int fd_s)
  : [fd_c:int] (accept_v fd_c | int fd_c)
  = "atslib_accept_null_err"

fun accept_null_exn {fd_s:int}
  (pf: !socket_v (fd_s, listen) | sockfd: int fd_s)
  : [fd_c:int] (socket_v (fd_c, conn) | int fd_c)
  = "atslib_accept_null_exn"

fun accept_ipv4_exn {fd_s:int} (
    pf: !socket_v (fd_s, listen)
  | sockfd: int fd_s
  , cliaddr: &sockaddr_in_struct_t? >> sockaddr_in_struct_t
  , addrlen: &socklen_t? >> socklen_t
  ) : [fd_c:int] (socket_v (fd_c, conn) | int fd_c)
  = "atslib_accept_ipv4_exn"

(* ****** ****** *)

dataview socket_close_v (fd: int, s: status, int) =
  | socket_close_fail (fd, s, ~1) of socket_v (fd, s)
  | socket_close_succ (fd, s, 0)

fun socket_close_err {fd:int} {s:status}
  (pf: socket_v (fd, s) | sockfd: int fd)
  : [i:int] (socket_close_v (fd, s, i) | int i)
  = "atslib_socket_close_err"

fun socket_close_exn {fd:int} {s:status}
  (pf: socket_v (fd, s) | sockfd: int fd): void
  = "atslib_socket_close_exn"

(* ****** ****** *)

fun socket_read_err {fd:int} {n,sz:nat | n <= sz} {l:addr}
  (pf_socket: !socket_v (fd, conn), pf_buf: !bytes sz @ l |
   sockfd: int fd, buf: ptr l, n: int n): intBtw(~1, n+1)
  = "atslib_socket_read_err"

fun socket_read_exn {fd:int} {n,sz:nat | n <= sz} {l:addr}
  (pf_socket: !socket_v (fd, conn), pf_buf: !bytes sz @ l |
   sockfd: int fd, buf: ptr l, n: int n): natLte n
  = "atslib_socket_read_exn"

(* ****** ****** *)

fun socket_write_err {fd:int} {n,sz:nat | n <= sz} {l:addr}
  (pf_socket: !socket_v (fd, conn), pf_buf: !bytes sz @ l |
   sockfd: int fd, buf: ptr l, n: int n): intBtw(~1, n+1)
  = "atslib_socket_write_err"

fun socket_write_exn {fd:int} {n,sz:nat | n <= sz} {l:addr}
  (pf_socket: !socket_v (fd, conn), pf_buf: !bytes sz @ l |
   sockfd: int fd, buf: ptr l, n: int n): natLte n
  = "atslib_socket_write_exn"

(* ****** ****** *)

fun socket_write_substring_err {fd:int} {i,n,sz:nat | i+n <= sz}
  (pf_socket: !socket_v (fd, conn) |
   sockfd: int fd, s: string sz, start: int i, n: int n): intBtw(~1, n+1)
  = "atslib_socket_write_substring_err"

fun socket_write_substring_exn {fd:int} {i,n,sz:nat | i+n <= sz}
  (pf_socket: !socket_v (fd, conn) |
   sockfd: int fd, s: string sz, start: int i, n: int n): natLte n
  = "atslib_socket_write_substring_exn"

(* ****** ****** *)

(* end of [socket.sats] *)
