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
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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

(*
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January, 2011
**
*)

(* ****** ****** *)
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at run-time
#define ATS_DYNLOADFLAG 0 // no dynloading at run-time

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "contrib/testing/SATS/fprint.sats"

(* ****** ****** *)

implement{a}
array_fprint_elt
  {n} (out, A, n, sep) = let
  var i: sizeLte (n); val _0 = size1_of_int1 (0)
in
  for (i := _0; i < n; i := i+1) (
    if i > 0 then fprint_string (out, sep); fprint_elt<a> (out, A.[i])
  ) // end of [for]
end // end of [array_fprint_elt]

(* ****** ****** *)

implement{a}
list_fprint_elt
  (out, xs, sep) = let
  fun loop (
    xs: List a, i: int
  ) :<cloref1> void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if i > 0 then
          fprint_string (out, sep)
        val () = fprint_elt<a> (out, x)
      in
        loop (xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (xs, 0)
end // end of [list_fprint_elt]

(* ****** ****** *)

implement{a}
list_vt_fprint_elt
  (out, xs, sep) = (
  list_fprint_elt<a> (out, $UN.castvwtp1 {List a} (xs), sep)
) // end of [list_vt_fprint_elt]

(* ****** ****** *)

(* end of [fprint.dats] *)
