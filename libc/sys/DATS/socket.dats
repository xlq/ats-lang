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

implement socket_read_loop_exn
  (pf_sock | fd, buf, ntotal) = let
  val nread = socket_read_loop_err (pf_sock | fd, buf, ntotal)
in
  if nread >= 0 then
    size1_of_ssize1 (nread)
  else begin
    perror "socket_read: "; exit 1
  end // end of [if]
end // end of [socket_read_loop]

implement socket_write_loop_exn
  (pf_sock | fd, buf, ntotal) = let
  var err: int = 1
  val nwrit = socket_write_loop_err (pf_sock | fd, buf, ntotal)
  val () = if nwrit >= 0 then let
    val nwrit = size1_of_ssize1 (nwrit)
  in
    if (nwrit = ntotal) then (err := 0)
  end // end of [if]
in
  if err > 0 then (perror "socket_write: "; exit 1) else ()
end // end of [socket_write_loop]

(* ****** ****** *)

(* end of [socket.dats] *)
