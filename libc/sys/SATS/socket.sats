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

%{#
#include "libc/sys/CATS/socket.cats"
%} // end of [%{#]

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
abst@ype sockaddr_in_struct = $extype "ats_sockaddr_in_type"

(* ****** ****** *)
//
// HX:
// client: init -> connect
// server: init -> bind -> listen -> accept
//
datasort status = init | bind | listen | conn

absview socket_v (int, status)

dataview socketopt_v (int) = 
  | socketopt_v_none (~1)
  | {fd:nat} socketopt_v_some (fd) of socket_v (fd, init)
// end of [socketopt_v]

fun socket_family_type_err
  (af: address_family_t, t: socket_type_t): [fd:int] (socketopt_v fd | int fd)
  = "atslib_socket_family_type_err"
// end of [socket_family_type_err]

fun socket_family_type_exn
  (af: address_family_t, t: socket_type_t): [fd:int] (socket_v (fd, init) | int fd)
  = "atslib_socket_family_type_exn"
// end of [socket_family_type_exn]

(* ****** ****** *)

fun sockaddr_ipv4_init (
    sa: &sockaddr_in_struct? >> sockaddr_in_struct
  , af: address_family_t, inp: in_addr_nbo_t, port: in_port_nbo_t
  ) :<> void = "atslib_sockaddr_ipv4_init"
// end of [sockaddr_ipv4_init]

(* ****** ****** *)

dataview connect_v (fd: int, int) =
  | connect_v_succ (fd,  0) of socket_v (fd, conn)
  | connect_v_fail (fd, ~1) of socket_v (fd, init)
// end of [connect_v]

fun connect_ipv4_err {fd:int} (
  pf_sock: socket_v (fd, init) | fd: int fd, servaddr: &sockaddr_in_struct
) : [i:int] (connect_v (fd, i) | int i)
  = "atslib_connect_ipv4_err"
// end of [connect_ipv4_err

fun connect_ipv4_exn {fd:int} (
    pf: !socket_v (fd, init) >> socket_v (fd, conn)
  | fd: int fd, servaddr: &sockaddr_in_struct
  ) : void = "atslib_connect_ipv4_exn"
// end of [connect_ipv4_exn]

(* ****** ****** *)

dataview bind_v (fd:int, int) = 
  | bind_v_fail (fd, ~1) of socket_v (fd, init)
  | bind_v_succ (fd,  0) of socket_v (fd, bind)
// end of [bind_v]

fun bind_ipv4_err {fd:int}
  (pf_sock: socket_v (fd, init) | fd: int fd, servaddr: &sockaddr_in_struct)
  : [i:int] (bind_v (fd, i) | int i)
  = "atslib_bind_ipv4_err"
// end of [bind_ipv4_err]

fun bind_ipv4_exn {fd:int} (
    pf_sock: !socket_v (fd, init) >> socket_v (fd, bind)
  | fd: int fd, servaddr: &sockaddr_in_struct
  ) : void = "atslib_bind_ipv4_exn"
// end of [bind_ipv4_exn]

(* ****** ****** *)

dataview listen_v (fd: int, int) = 
  | listen_v_fail (fd, ~1) of socket_v (fd, bind) 
  | listen_v_succ (fd,  0) of socket_v (fd, listen)
// end of [listen_v]

fun listen_err {fd:int}
  (pf_sock: socket_v (fd, bind) | fd: int fd, backlog: Pos)
  : [i:int] (listen_v (fd, i) | int i)
  = "atslib_listen_err"
// end of [listen_err]

fun listen_exn {fd:int} (
    pf_sock: !socket_v (fd, bind) >> socket_v (fd, listen)
  | fd: int fd, backlog: Pos // [backlog = 0] is not supported on all systems
  ) : void  = "atslib_listen_exn"
// end of [listen_exn]

(* ****** ****** *)

dataview accept_v (int) = 
  | {fd:nat} accept_v_succ (fd) of socket_v (fd, conn)
  | accept_v_fail (~1)
// end of [accept_v]

fun accept_null_err {fd_s:int}
  (pf_sock: !socket_v (fd_s, listen) | fd_s: int fd_s)
  : [fd_c:int] (accept_v fd_c | int fd_c)
  = "atslib_accept_null_err"
// end of [accept_null_err]

fun accept_null_exn {fd_s:int}
  (pf_sock: !socket_v (fd_s, listen) | fd_s: int fd_s)
  : [fd_c:int] (socket_v (fd_c, conn) | int fd_c)
  = "atslib_accept_null_exn"
// end of [accept_null_exn]

fun accept_ipv4_exn {fd_s:int} (
    pf_sock: !socket_v (fd_s, listen)
  | fd_s: int fd_s
  , cliaddr: &sockaddr_in_struct? >> sockaddr_in_struct
  , addrlen: &socklen_t? >> socklen_t
  ) : [fd_c:int] (socket_v (fd_c, conn) | int fd_c)
  = "atslib_accept_ipv4_exn"
// end of [accept_ipv4_exn]

(* ****** ****** *)

dataview socket_close_v (fd: int, s: status, int) =
  | socket_close_v_fail (fd, s, ~1) of socket_v (fd, s)
  | socket_close_v_succ (fd, s, 0)
// end of [socket_close_v]

fun socket_close_err {fd:int} {s:status}
  (pf_sock: socket_v (fd, s) | fd: int fd)
  : [i:int] (socket_close_v (fd, s, i) | int i)
  = "atslib_socket_close_err"
// end of [socket_close_err]

fun socket_close_exn {fd:int} {s:status}
  (pf_sock: socket_v (fd, s) | fd: int fd): void
  = "atslib_socket_close_exn"
// end of [socket_close_exn]

(* ****** ****** *)
//
// HX: implemented in [libc/CATS/fcntl.cats]
//
fun socket_read_err {fd:int} {n,sz:nat | n <= sz} (
    pf_sock: !socket_v (fd, conn) | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : ssizeBtw(~1, n+1) = "atslib_fildes_read_err"
// end of [socket_read_err]
//
// HX: implemented in [libc/sys/DATSsocket.dats]
//
fun socket_read_exn {fd:int} {n,sz:nat | n <= sz} (
    pf_sock: !socket_v (fd, conn) | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : sizeLte n
// end of [socket_read_exn]

(* ****** ****** *)
//
// HX:
// this one is implemented in [libc/DATS/fcntl.dats]
// note that it is used only when it is known ahead how many bytes are expected;
// otherwise, there is the risk of forever blocking!!!
//
fun socket_read_loop_err {fd:int} {n,sz:nat | n <= sz} (
    pf_sock: !socket_v (fd, conn) | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : ssizeBtw (~1, n+1) = "atslib_fildes_read_loop_err"
// end of [socket_read_loop_err]

(* ****** ****** *)
//
// HX: implemented in [libc/CATS/fcntl.cats]
//
fun socket_write_err {fd:int} {n,sz:nat | n <= sz} (
    pf_sock: !socket_v (fd, conn) | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : ssizeBtw(~1, n+1) = "atslib_fildes_write_err"
// end of [socket_write_err]

(* ****** ****** *)
//
// HX: implemented in [libc/DATS/fcntl.dats]
//
fun socket_write_loop_err {fd:int} {n,sz:nat | n <= sz} (
    pf_sock: !socket_v (fd, conn) | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : ssizeBtw(~1, n+1) = "atslib_fildes_write_loop_err"
// end of [socket_write_loop_err]
//
// HX: implemented in [libc/sys/DATS/socket.dats]
//
fun socket_write_loop_exn {fd:int} {n,sz:nat | n <= sz} (
    pf_sock: !socket_v (fd, conn) | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : void // all bytes must be written if this function returns
  = "atslib_socket_write_loop_exn"
// end of [socket_write_loop_exn]

(* ****** ****** *)

(* end of [socket.sats] *)
