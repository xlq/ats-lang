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

staload "libc/SATS/string.sats"
staload "libc/SATS/stdlib.sats"

(* ****** ****** *)

implement
putenv (nameval) = let
  val (pfgc, pfbuf | p) =
    strdup_ngc (__cast nameval) where {
    extern castfn __cast {l:agz} (x: !strptr l): String
  } // end of [val]
  prval () = __assert (pfgc) where {
    extern prfun __assert {v:view} (pf: v):<> void
  } // end of [prval]
  val err = __putenv (pfbuf | p) where {
    extern fun __putenv {m,n:int} {l:addr}
      (pf: strbuf (m, n) @ l | p: ptr l): int = "#putenv"
  } // end of [val]
  val () = let
    extern fun __free (p: ptr): void = "atspre_free_ngc" // in case ...
  in
    if (err <> 0) then __free (p) // [putenv] failed
  end // end of [val]
in
  err (* z/nz : succ/fail *)
end // end of [putenv]

(* ****** ****** *)

(* end of [stdlib.dats] *)
