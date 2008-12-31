(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
**
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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
**
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

staload "libc/SATS/errno.sats"

(* ****** ****** *)

staload "libc/SATS/fcntl.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading is needed

(* ****** ****** *)

implement close_exn {fd} {flag} (pf_fd | fd) = let
  fun loop
    (pf_fd: fildes_v (fd, flag) | fd: int fd): void = let
    val (pf | i) = close_err (pf_fd | fd)
  in
    if i >= 0 then let
      prval close_v_succ () = pf // [i] actually equals 0
    in
      // loop exits
    end else let
      prval close_v_fail pf_fd = pf
      // try again only if [close] is interrupted by a signal
      val () = if errno_get () <> EINTR then exit {void} (1)
    in
      loop (pf_fd | fd)
    end // end of [if]
  end // end of [loop]
in
  loop (pf_fd | fd)
end // end of [close_exn]

(* ****** ****** *)

(* end of [fcntl.dats] *)
