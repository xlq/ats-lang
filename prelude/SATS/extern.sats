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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: January 29, 2010

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

//
// HX: this file is mostly used for building API's for external packages.
// The "tricks" presented here should be used sparringly in cases that do
// require special attention.
//

(* ****** ****** *)

viewdef ptrout
  (a:viewt@ype, l:addr) = (a @ l, a @ l -<lin,prf> void)
// end of [ptrout]
viewdef ptroutopt
  (a:viewt@ype, l:addr) = option_v (ptrout (a, l), l > null)
// end of [ptroutopt]

(* ****** ****** *)

//
// HX: note that (vt1 \minus v2) roughly means that a ticket of
// [v2] is taken from [vt1]; the ticket must be returned before
// [vt1] is consumed.
//
absview minus_viewt0ype_view (vt1: viewt@ype, v2: view) = vt1
stadef minus = minus_viewt0ype_view
prfun minus_addback // [minus] is defined in basics_sta.sats
  {vt1:viewt@ype} {v2:view} (pf1: minus (vt1, v2), pf2: v2 | x: !vt1): void
// end of [minus_addback]

(* ****** ****** *)

//
// HX-2010-04-18:
// the types [stamp] and [stamped] should only be used in a situation where
// the value takeout out cannot be uniquely identified by its type
//
absviewtype
stamped (a:viewtype, l:addr) = a
prfun stamped_encode
  {a:viewtype} (x: !a >> stamped (a, l)):<> #[l:addr] void
// end of [stamped_encode]
prfun stamped_decode
  {a:viewtype} {l:addr} (x: !stamped (a, l) >> a):<> void
// end of [stamped_decode]

absviewtype
stamp (a:viewtype, l:addr) = a
castfn stamp_get
  {a:viewtype} {l:addr} (x: !a >> stamped (a, l))
  : (minus (stamped (a, l), stamp (a, l)) | stamp (a, l))
// end of [stamp_get]
castfn stamp_get1
  {a:viewtype} {l:addr} (x: !stamped (a, l))
  : (minus (stamped (a, l), stamp (a, l)) | stamp (a, l))
// end of [stamp_get1]

(* ****** ****** *)

(* end of [extern.sats] *)
