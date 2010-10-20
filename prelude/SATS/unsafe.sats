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
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
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
// Time: October, 2010
//
(* ****** ****** *)
//
// HX: these unsafe features must be used with caution!!!
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // there is no need for staloading at run-time

(* ****** ****** *)
//
// HX: the generic ones:
//
castfn cast {to:t@ype} {from:t@ype} (x: from):<> to
praxi castvw {to:view} {from:view} (x: from):<> to
praxi castvw1 {to:view} {from:view} (x: !from):<> to
castfn castvwtp {to:viewt@ype} {from:viewt@ype} (x: from):<> to
castfn castvwtp1 {to:viewt@ype} {from:viewt@ype} (x: !from):<> to

(* ****** ****** *)

castfn cast2int {a:t@ype} (x: a):<> int
castfn cast2uint {a:t@ype} (x: a):<> uint
castfn cast2lint {a:t@ype} (x: a):<> lint
castfn cast2ulint {a:t@ype} (x: a):<> ulint
castfn cast2size {a:t@ype} (x: a):<> size_t
castfn cast2ssize {a:t@ype} (x: a):<> ssize_t

(* ****** ****** *)

fun{a:viewt@ype} ptrget {l:agz} (p: ptr l): a
fun{a:viewt@ype} ptrset {l:agz} (p: ptr l, x: a): void

(* ****** ****** *)

(* end of [unsafe.sats] *)
