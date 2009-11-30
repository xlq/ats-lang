(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: July 2007

(* ****** ****** *)

(* ats_error: some common error reporting functions *)

(* ****** ****** *)

staload "ats_location.sats"

(* ****** ****** *)

staload "ats_error.sats"

(* ****** ****** *)

implement abort () = let
(*
  val _ = segfault () where {
    extern fun segfault (): int = "ats_error_segfault"
  } // end of [val]
*)
in
  $raise FatalErrorException ()
end

(*
implement error msg = begin
  prerr (msg) ; prerr_newline () ; $raise FatalErrorException ()
end

implement error_location (loc, msg) = begin
  prerr_location loc ; prerr ": " ; prerr msg ; prerr_newline () ;
  $raise FatalErrorException ()
end
*)

implement deadcode msg = begin
  prerr "error(deadcode)";
  prerr (msg); prerr_newline (); $raise DeadCodeException ()
end // end of [deadcode]

(* ****** ****** *)

%{$

ats_int_type ats_error_segfault () {
  fprintf (stderr, "ats_error_segfault: this is for debugging.\n") ;
  return *(ats_int_type*)0 ;
} /* end of [ats_error_segfault] */

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_error.dats] *)
