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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

implement{a}
slist_foreach_clo 
  (pf | xs, f) =
  if slist_isnot_nil (xs) then let
    val (pfat | xs1) = slist_uncons (xs)
    val p = ptr_of {a} (xs)
    val () = f (pf | !p)
    val () = slist_foreach_clo (pf | xs1, f)
    prval () = slist_fold {a} (pfat | xs, xs1)
  in
    // nothing
  end else ()
// end of [slist_foreach_clo]

(* ****** ****** *)

(* end of [slist.dats] *)
