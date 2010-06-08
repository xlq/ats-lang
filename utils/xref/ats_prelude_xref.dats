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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
// Time: March 2009
//
(* ****** ****** *)

//
// This file is solely for generating cross-references to
// static and dynamic constants declared in various files
// in the directory [$ATSHOME/prelude]/
//
// A typical use is like this:

// atsopt --posmark_xref=XREF -d ats_prelude_xref.dats > /dev/null

// where [XREF] should be replaced with the name of a directory
// that is already created for storing the files that are to be
// generated for cross-referencing.
//

(* ****** ****** *)

staload _ = "prelude/sortdef.sats"
staload _ = "prelude/basics_sta.sats"
staload _ = "prelude/basics_dyn.sats"
staload _ = "prelude/macrodef.sats"

staload _ = "prelude/SATS/arith.sats"
staload _ = "prelude/SATS/vsubrw.sats"

staload _ = "prelude/SATS/bool.sats"
staload _ = "prelude/SATS/byte.sats"
staload _ = "prelude/SATS/char.sats"

staload _ = "prelude/SATS/extern.sats"

staload _ = "prelude/SATS/file.sats"
staload _ = "prelude/SATS/float.sats"
staload _ = "prelude/SATS/integer.sats"
staload _ = "prelude/SATS/integer_fixed.sats"
staload _ = "prelude/SATS/integer_ptr.sats"
staload _ = "prelude/SATS/lazy.sats"
staload _ = "prelude/SATS/lazy_vt.sats"
staload _ = "prelude/SATS/memory.sats"
staload _ = "prelude/SATS/pointer.sats"
staload _ = "prelude/SATS/printf.sats"
staload _ = "prelude/SATS/reference.sats"
staload _ = "prelude/SATS/sizetype.sats"
staload _ = "prelude/SATS/string.sats"

staload _ = "prelude/SATS/array.sats"
staload _ = "prelude/SATS/array0.sats"
staload _ = "prelude/SATS/list.sats"
staload _ = "prelude/SATS/list0.sats"
staload _ = "prelude/SATS/list_vt.sats"
staload _ = "prelude/SATS/matrix.sats"
staload _ = "prelude/SATS/matrix0.sats"
staload _ = "prelude/SATS/option.sats"
staload _ = "prelude/SATS/option0.sats"
staload _ = "prelude/SATS/slseg.sats"

(* ****** ****** *)

(* end of [ats_prelude_xref.dats] *)
