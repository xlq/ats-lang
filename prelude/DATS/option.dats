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

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

// this is a casting function
implement option_of_option_vt (ov) = case+ ov of
  | ~Some_vt (v) => Some (v) | ~None_vt () => None ()
// end of [option_of_option_vt]

(* ****** ****** *)

implement option_is_none (ov) = case+ ov of
  | None () => true | Some _ => false

implement option_is_some (ov) = case+ ov of
  | Some _ => true | None () => false

implement{a} option_some v = Some v
implement{a} option_unsome ov = let val Some v = ov in v end

implement{a} option_app (ov, f) =
  case+ ov of Some v => f v | None () => ()

implement{a,b} option_map (ov, f) =
  case+ ov of Some v => Some (f v) | None () => None

(* ****** ****** *)

// [option.sats] is already loaded by a call to [pervasive_load]
staload _(*anonymous*) = "prelude/SATS/option.sats" // this forces that the static
// loading function for [option.sats] is to be called at run-time
// this is really needed only if some datatypes are declared in [option.sats]

(* ****** ****** *)

(* end of [option.dats] *)
