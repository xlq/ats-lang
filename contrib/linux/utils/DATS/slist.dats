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

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0

(* ****** ****** *)

staload "contrib/linux/utils/SATS/slist.sats"

(* ****** ****** *)

implement
slist_make_nil
  {a} () = __cast (null) where {
  extern castfn __cast (p: ptr null):<> slist (a, 0, null)
} // end of [slist_make_nil]

implement
slseg_free_nil
  {a} {la,lz} (xs) = let
  val ptr = ptrnul_of (xs) in (* nothing *)
end // end of [slist_free_nil]

(* ****** ****** *)

implement{a}
slist_length (xs) = let
  fun loop {i,j:nat}
    {la:addr} .<i>. (
    xs: !slist (a, i, la), j: size_t (j)
  ) :<> size_t (i+j) =
    if slist_isnot_nil (xs) then let
      val (pfat | xs1) = slseg_uncons (xs)
      val res = loop (xs1, j+1)
      prval () = slseg_fold (pfat | xs, xs1)
    in
      res
    end else j // end of [if]
  // end of [loop]
in
  loop (xs, 0)
end // end of [slist_length]

(* ****** ****** *)

implement{a}
slseg_split
  {n,i} {la,lz} (xs, i) = let
  extern castfn split0 (
    xs: !slseg (a, n, la, lz) >> slseg (a, 0, la, la)
  ) :<> slseg (a, n, la, lz)
in
  if i > 0 then let
    val (pfat | xs1) = slseg_uncons<a> (xs)
    val res = slseg_split (xs1, i-1)
    prval () = slseg_fold (pfat | xs, xs1)
  in
    res
  end else
    split0 (xs)
  // end of [if]
end // end of [slist_split]

implement{a}
slist_split
  {n,i} {la} (xs, i) = let
  extern castfn split0 (
    xs: !slist (a, n, la) >> slseg (a, 0, la, la)
  ) :<> slist (a, n, la)
in
  if i > 0 then (
    if slist_isnot_nil (xs) then let
      val (pfat | xs1) = slseg_uncons<a> (xs)
      val res = slist_split (xs1, i-1)
      prval () = slseg_fold (pfat | xs, xs1)
    in
      res
    end else
      slist_make_nil ()
    // end of [if]
  ) else split0 (xs)
end // end of [slist_split]

(* ****** ****** *)

implement{a}
slist_foreach_clo 
  (pf | xs, f) =
  if slist_isnot_nil (xs) then let
    val p = ptr_of {a} (xs)
    val (pfat | xs1) = slseg_uncons (xs)
    val () = f (pf | !p)
    val () = slist_foreach_clo (pf | xs1, f)
    prval () = slseg_fold {a} (pfat | xs, xs1)
  in
    // nothing
  end else ()
// end of [slist_foreach_clo]

(* ****** ****** *)

(* end of [slist.dats] *)
