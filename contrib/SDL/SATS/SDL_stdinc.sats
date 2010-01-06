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

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: January, 2010

(* ****** ****** *)

abst@ype Sint8 = int8_t0ype
abst@ype Uint8 = uint8_t0ype

abst@ype Sint16 = int16_t0ype
abst@ype Uint16 = uint16_t0ype

(* ****** ****** *)

abst@ype Sint32 = int32_t0ype
abst@ype Uint32 = uint32_t0ype

castfn Sint32_of_int (x: int):<> Sint32
overload Sint32 with Sint32_of_int

castfn Uint32_of_int (x: int):<> Uint32
overload Uint32 with Uint32_of_int

castfn Uint32_of_uint (x: uint):<> Uint32
overload Uint32 with Uint32_of_uint

(* ****** ****** *)

abst@ype Sint64 = int64_t0ype
abst@ype Uint64 = uint64_t0ype

(* ****** ****** *)

(* end of [SDL_stdinc.sats] *)
