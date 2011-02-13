(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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
// Start Time: August 2007
//
(* ****** ****** *)

staload Fil = "ats_filename.sats"

(* ****** ****** *)

local

staload "ats_syntax.sats"

in // in of [local]

datatype yyres =
  | YYRESs0exp of s0exp
  | YYRESd0exp of d0exp
  | YYRESd0eclst of d0eclst
// end of [yyres]

typedef d0eclst = d0eclst

fun yyres_s0exp (s0e: s0exp): yyres = "atsopt_yyres_s0exp"
fun yyres_d0exp (d0e: d0exp): yyres = "atsopt_yyres_d0exp"
fun yyres_d0eclst (d0cs: d0eclst): yyres = "atsopt_yyres_d0eclst"

end // end of [local]

(* ****** ****** *)

datatype yybeg =
  | YYBEGnone of ()
  | YYBEGs0exp of ()
  | YYBEGd0exp of ()
  | YYBEGd0ecseq_sta of ()
  | YYBEGd0ecseq_dyn of ()
// end of [yybeg]

(* ****** ****** *)

fun parse_from_stdin_yyres (tok: yybeg): yyres
fun parse_from_stdin_d0eclst (flag: int): d0eclst

(* ****** ****** *)

fun parse_from_filename_yyres (tok: yybeg, fil: $Fil.filename_t): yyres
fun parse_from_filename_d0eclst (flag: int, fil: $Fil.filename_t): d0eclst

(* ****** ****** *)

fun parse_from_string_yyres (tok: yybeg, str: string): yyres

(* ****** ****** *)

(* end of [ats_parser.sats] *)
