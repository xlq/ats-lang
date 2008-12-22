(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

// Time: Summer 2007

(* Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{^

#include "libc/CATS/stdio.cats"
#include "libc/CATS/stdlib.cats"
#include "libc/sys/CATS/types.cats"
#include "libc/CATS/unistd.cats"

%}

(* ****** ****** *)

staload "top.sats"

(* ****** ****** *)

fn do_usage (cmd: string): void = begin
  printf ("The usage of %s is:\n", @(cmd));
  printf ("  1. %s -all (* generating [libats.a] *)\n", @(cmd));
  printf ("  2. %s [infile] (* compiling and archiving a single file *) \n", @(cmd));
end

//

dynload "basics.dats"
dynload "atscc.dats"
dynload "atslib.dats"

//

implement main_prelude () = ()

//

implement main (argc, argv) = begin
  if argc > 1 then begin
    case+ argv.[1] of
      | "-all" => libats_make ()
      | "-lex" => libatslex_make ()
      | infile => ccomp_gcc_ar_libfile (infile, libats_global)
  end else begin
    do_usage argv.[0]
  end // end of [if]
end // end of [main]

(* ****** ****** *)

(* end of [atslib_main.dats] *)
