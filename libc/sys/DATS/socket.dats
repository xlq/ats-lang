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
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
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
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

staload "libc/SATS/stdio.sats" // for [perror]

(* ****** ****** *)

staload "libc/sys/SATS/socket.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

extern praxi bytes_v_split {n,i:nat | i <= n}
  {l:addr} (pf: bytes n @ l): @(bytes i @ l, bytes (n-i) @ l + i)

extern praxi bytes_v_unsplit {n1,n2:nat}
  {l:addr} (pf1: bytes n1 @ l, pf2: bytes n2 @ l + n1): bytes (n1+n2) @ l

implement socket_read_loop_err
  {fd} {n,sz} (pf_sock, pf_buf | fd, p_buf, ntotal) = let
  fun loop {nleft:nat | nleft <= n} {l:addr} .<nleft>. (
      pf_sock: !socket_v (fd, conn)
    , pf_buf: !bytes (sz-n+nleft) @ l
    | fd: int fd, p_buf: ptr l, nleft: int nleft, err: &int
    ) : natLte n =
    if nleft > 0 then let
      val [nread:int] nread = socket_read_err (pf_sock, pf_buf | fd, p_buf, nleft)
    in
      if nread > 0 then let
        prval @(pf1_buf, pf2_buf) = bytes_v_split {sz-n+nleft,nread} (pf_buf)
        val nleft2 = loop (pf_sock, pf2_buf | fd, p_buf + nread, nleft - nread, err)
        prval () = pf_buf := bytes_v_unsplit (pf1_buf, pf2_buf)
      in
        nleft2
      end else let // nread <= 0
        val () = if nread < 0 then (err := 1) // should a retry be automatic if
        // this is caused by EINTR?
      in
        nleft // no more bytes read or an error occurred
      end // end of [if]
    end else begin
      0 // all bytes are read
    end // end of [if]
  // end of [loop]
  var err: int = 0; val nleft = loop (pf_sock, pf_buf | fd, p_buf, ntotal, err)
in
  if err = 0 then ntotal - nleft else ~1
end // end of [socket_read_loop_exn]

//

implement socket_read_loop_exn
  (pf_sock, pf_buf | fd, p_buf, ntotal) = let
  val nread = socket_read_loop_err (pf_sock, pf_buf | fd, p_buf, ntotal)
in
  if nread >= 0 then nread else (perror "socket_read: "; exit 1)
end // end of [socket_read_loop]

(* ****** ****** *)

implement socket_write_loop_err
  {fd} {n,sz} (pf_sock, pf_buf | fd, p_buf, ntotal) = let
  fun loop {nleft:nat | nleft <= n} {l:addr} .<nleft>. (
      pf_sock: !socket_v (fd, conn)
    , pf_buf: !bytes (sz-n+nleft) @ l
    | fd: int fd, p_buf: ptr l, nleft: int nleft, err: &int
    ) : natLte n =
    if nleft > 0 then let
      val [nwrit:int] nwrit = socket_write_err (pf_sock, pf_buf | fd, p_buf, nleft)
    in
      if nwrit > 0 then let
        prval @(pf1_buf, pf2_buf) = bytes_v_split {sz-n+nleft,nwrit} (pf_buf)
        val nleft2 = loop (pf_sock, pf2_buf | fd, p_buf + nwrit, nleft - nwrit, err)
        prval () = pf_buf := bytes_v_unsplit (pf1_buf, pf2_buf)
      in
        nleft2
      end else let // nwrit <= 0
        val () = if nwrit < 0 then (err := 1) // should a retry be automatic if
        // this is caused by EINTR?
      in
        nleft // no more bytes written or an error occurred
      end // end of [if]
    end else begin
      0 // all bytes are written
    end // end of [if]
  // end of [loop]
  var err: int = 0; val nleft = loop (pf_sock, pf_buf | fd, p_buf, ntotal, err)
in
  if err = 0 then ntotal - nleft else ~1
end // end of [socket_read_loop_exn]

//

implement socket_write_loop_exn
  (pf_sock, pf_buf | fd, p_buf, ntotal) = let
  val nwrit = socket_write_loop_err (pf_sock, pf_buf | fd, p_buf, ntotal)
in
  if nwrit < ntotal then (perror "socket_write: "; exit 1) else ()
end // end of [socket_write_loop]

(* ****** ****** *)

(* end of [socket.dats] *)
