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

// July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "top.sats"

(* ****** ****** *)

dynload "intset.dats"
dynload "charset.dats"
dynload "states.dats"

dynload "position.dats"
dynload "token.dats"

dynload "parser.dats"
dynload "lexgen.dats"

implement main (argc, argv) = let

val () = let
  val (pf_stdin | p_stdin) = stdin_get ()
in
  the_atslex_input_set (pf_stdin | p_stdin)
end // end of [val]

val () = token_initialization ()

// val () = prerr ("atslex: [lexer_parse] is started.\n")

val lexer = lexer_parse ()

// val () = prerr ("atslex: [lexer_parse] is finished.\n")

val (pf_stdout | ptr_stdout) = stdout_get ()

val () = fprint_string (
  file_mode_lte_w_w | !ptr_stdout, lexer.preamble
)

// val () = prerr ("atslex: preamble is finished.\n")

val () = fprint_lexfns (
  file_mode_lte_w_w | !ptr_stdout, lexer.redef, lexer.lexfns
)

// val () = prerr ("atslex: [fprint_lexfns] is finished.\n")

val () = fprint_string (
  file_mode_lte_w_w | !ptr_stdout, lexer.postamble
)

// val () = prerr ("atslex: postamble is finished.\n")

in

stdout_view_set (pf_stdout | (*none*))

end

(* ****** ****** *)

(* end of [atslex.dats] *)
