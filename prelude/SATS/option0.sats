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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [option.sats] starts!\n"

#endif

(* ****** ****** *)

// a casting function implemented in [prelude/DATS/option.cats]
castfn option0_of_option1 {a:t@ype} (xs: List a):<> option0 a
  = "atspre_option0_of_option1"

// a casting function implemented in [prelude/DATS/option.cats]
castfn option1_of_option0 {a:t@ype} (xs: option0 a):<> List a
  = "atspre_option1_of_option0"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [option0.sats] finishes!\n"

#endif

(* end of [option0.sats] *)
