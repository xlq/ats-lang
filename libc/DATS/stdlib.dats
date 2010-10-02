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
putenv {l} (nameval) = let
  val n = strptr_length (nameval)
  val [n:int] n = size1_of_size (n)
  val [l1:addr] (pfopt | p) = malloc_ngc (n + 1)
in
  if p > null then let
    prval malloc_v_succ (pfngc, pfbuf) = pfopt
    val _p = __copy (pfbuf | p, nameval) where {
      extern fun __copy (
        pf: !b0ytes (n+1) @ l1 >> strbuf (n+1, n) @ l1 | p: ptr l1, name: !strptr l
      ) :<> void = "#atslib_strcpy"
    } // end of [val]
    prval () = __assert (pfngc) where {
      extern prfun __assert {v:view} (pf: v):<> void
    } // end of [prval]
    val err = __putenv (pfbuf | p) where {
      extern fun __putenv {m,n:int} {l:addr}
        (pf: strbuf (n+1, n) @ l1 | p: ptr l1): int = "#putenv"
    } // end of [val]
    val () = let
      extern fun __free (p: ptr): void = "atspre_free_ngc" // in case ...
    in
      if (err <> 0) then __free (p) // [putenv] failed
    end // end of [val]
  in
    err
  end else let
    prval malloc_v_fail () = pfopt in ~1 // HX: [ENOMEM] should be set
  end (* end of [if] *)
end // end of [putenv]

(* ****** ****** *)

(* end of [stdlib.dats] *)
