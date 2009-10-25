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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August 2007

(* ****** ****** *)

%{^

#include "libc/CATS/stdio.cats"

%}

(* ****** ****** *)

// staload "libc/SATS/stdio.sats"

extern fun fopen_exn {m:file_mode}
  (s: string, m: file_mode m): [l:addr] (FILE m @ l | ptr l)
  = "atslib_fopen_exn"

(* ****** ****** *)

staload Fil = "ats_filename.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_lexer.sats"
staload "ats_parser.sats"

(* ****** ****** *)

staload LEXING = "libats_lex_lexing.sats"

(* ****** ****** *)

extern fun yyparse_main (tok0: token_t): $Syn.d0eclst = "yyparse_main"

fn flag_is_sta (flag: int): bool = (flag = 0)
fn flag_is_dyn (flag: int): bool = (flag > 0)

implement parse_from_filename (flag, filename) = let
(*
  val () = begin
    prerr "parse_from_filename: "; $Fil.prerr_filename filename; prerr_newline ()
  end // end of [val]
*)
  val fullname = $Fil.filename_full filename
  val file_mode_r = $extval (file_mode r, "\"r\"")
  val (pf_fil | p_fil) = fopen_exn (fullname, file_mode_r)
  val (pf_infil | p_infil) =
    $LEXING.infile_make_file (pf_fil, file_mode_lte_r_r | p_fil)
  val (pf_lexbuf | lexbuf) =
    $LEXING.lexbuf_make_infile (pf_infil | p_infil)
  val () = $LEXING.lexing_lexbuf_set (pf_lexbuf | lexbuf)
  var tok0: token_t = ISNONE
  val () = if flag_is_sta flag then tok0 := ISSTATIC
  val () = if flag_is_dyn flag then tok0 := ISDYNAMIC
  val ans = yyparse_main (tok0)
in
  $LEXING.lexing_lexbuf_free (); ans
end // end of [parse_from_filename]

implement parse_from_stdin (flag) = let
  val (pf_infil | p_infil) = $LEXING.infile_make_stdin ()
  val (pf_lexbuf | lexbuf) =
    $LEXING.lexbuf_make_infile (pf_infil | p_infil)
  val () = $LEXING.lexing_lexbuf_set (pf_lexbuf | lexbuf)
  var tok0: token_t = ISNONE
  val () = if flag_is_sta flag then tok0 := ISSTATIC
  val () = if flag_is_dyn flag then tok0 := ISDYNAMIC
  val ans = yyparse_main (tok0)
in
  $LEXING.lexing_lexbuf_free (); ans
end // end of [parse_from_stdin]

(* ****** ****** *)

(* end of [ats_parser.dats] *)
