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
 * Copyright (C) 2002-2009 Hongwei Xi, Boston University
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

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload STDIO = "libc/SATS/stdio.sats"

(* ****** ****** *)

staload Loc = "location.sats"
staload Sym = "symbol.sats"
staload Tok = "atsyacc_token.sats"

(* ****** ****** *)

typedef sym = $Sym.symbol_t
typedef symopt = Option (sym)

typedef token = $Tok.token
typedef tokenlst = List (token)
typedef tokenopt = Option (token)

(* ****** ****** *)

staload "atsyacc_top.sats"

(* ****** ****** *)

staload _(*anonymois*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

extern fun the_token_get (): token
extern fun the_token_update (): void
extern fun the_token_update_get (): token
extern fun the_token_get_update (): token

extern fun the_assocval_get_inc (): int

extern fun the_startsym_get (): symopt
extern fun the_startsym_set (symopt: symopt): void

local

val theTokenRef = let
  val tok = $Tok.token_none_make () in ref_make_elt<token> (tok)
end // end of [val]

val theAssocValRef = ref_make_elt<int> (0)

val theStartSymRef = ref_make_elt<symopt> (None)

in // in of [loca]

implement the_token_get () = !theTokenRef

implement the_token_update () = let
  val tok = atsyacc_lexer_token_get () in !theTokenRef := tok
end // end of [the_token_update]

implement the_token_get_update () = let
  val tok0 = !theTokenRef
  val tok1 = atsyacc_lexer_token_get () in !theTokenRef := tok1; tok0
end // end of [the_token_update]

implement the_token_update_get () = let
  val tok = atsyacc_lexer_token_get () in !theTokenRef := tok; tok
end // end of [the_token_update]

implement the_assocval_get_inc () = let
  val n = !theAssocValRef in !theAssocValRef := n+1; n
end // end of [the_assoc_get_inc]

implement the_startsym_get () = !theStartSymRef
implement the_startsym_set (symopt) = !theStartSymRef := symopt

end // end of [local]

(* ****** ****** *)

fn parse_percperc (): void = let
  val tok = the_token_get () in
  case+ tok.token_node of
  | $Tok.TOKpercperc () => the_token_update ()
  | _ => begin
      prerr "The token at [";
      $Loc.prerr_location tok.token_loc;
      prerr "] should be [%%] but it is not.";
      prerr_newline ();
      exit {void} (1)
    end // end of [_]
end // end of [parse_percperc]

fn parse_percpercopt (): void = let
  val tok = the_token_get () in
  case+ tok.token_node of
  | $Tok.TOKpercperc () => the_token_update ()
  | _ => ()
end // end of [parse_percpercopt]

(* ****** ****** *)

fun parse_type (): token = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKptbrackstr _ => let
      val () = the_token_update () in tok
    end // end of [TOKptbrackstr]
  | _ => begin
      prerr "The token at [";
      $Loc.prerr_location tok.token_loc;
      prerr "] should represent a type but it does not.";
      prerr_newline ();
      exit {token} (1)
    end // end of [_]
end // end of [parse_typeopt]

fun parse_typeopt (): tokenopt = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKptbrackstr _ => let
      val () = the_token_update () in Some (tok)
    end // end of [TOKptbrackstr]
  | _ => None ()
end // end of [parse_typeopt]

(* ****** ****** *)

fun parse_tokenlst
  (tpopt: tokenopt): void = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKident name => let
      val () = the_token_update ()
      val isnew = $Sym.name_is_new (name)
    in
      if isnew then let
        val _(*sym*) = $Sym.symbol_make_newname (name)
      in
        parse_tokenlst (tpopt)
      end else begin
        prerr "The token at [";
        $Loc.prerr_location tok.token_loc;
        prerr "] is introduced repeatedly.";
        prerr_newline ();
        exit {void} (1)
      end // end of [if]
    end // end of [parse_tokenlst]
  | _ => ()
end // end of [parse_tokenlst] 

(* ****** ****** *)

fun parse_assoclst (assoc: int): void = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKident name => let
      val () = the_token_update ()
      val sym = $Sym.symbol_make_name (name)
      val () = $Sym.symbol_assoc_set (sym, assoc)
    in
      parse_assoclst (assoc)
    end // end of [parse_assoclst]
  | _ => ()
end // end of [parse_assoclst]

(* ****** ****** *)

fun parse_start (): void = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKident name => let
      val () = the_token_update ()
      val sym = $Sym.symbol_make_name (name)
    in
      the_startsym_set (Some sym)
    end // end of [TOKident]
  | _ => ()
end // end of [parse_start]

(* ****** ****** *)

fn name_is_leftassoc (name: string): bool =
  case+ name of
  | "%left" => true
  | "%leftassoc" => true
  | _ => false
// end of [name_is_leftassoc]

fn name_is_rightassoc (name: string): bool =
  case+ name of
  | "%right" => true
  | "%rightassoc" => true
  | _ => false
// end of [name_is_rightassoc]

fn parse_keyword_line (flag: &int): void = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKkeyword name => let
      val () = flag := flag + 1
      val () = the_token_update ()
    in
      case+ name of
      | _ when (name = "%token") => let
          val tpopt = parse_typeopt ()
        in
          parse_tokenlst (tpopt)
        end // end of ["%token"]
      | _ when (name = "%nonassoc") => let
          val n = the_assocval_get_inc () in
          parse_assoclst (3 * n)
        end
      | _ when (name_is_leftassoc name) => let
          val n = the_assocval_get_inc () in
          parse_assoclst (3 * n + 1)
        end
      | _ when (name_is_rightassoc name) => let
          val n = the_assocval_get_inc () in
          parse_assoclst (3 * n + 2)
        end
      | _ when (name = "%type") => let
          val tp = parse_type ()
        in
          parse_tokenlst (Some tp)
        end
      | _ when (name = "%start") => parse_start ()
      | _ => begin
          prerr "The keyword at [";
          $Loc.prerr_location tok.token_loc;
          prerr "] is unrecognized.";
          prerr_newline ();
          exit {void} (1)
        end // end of [_]
    end // end of [TOKkeyword]
  | _ => ()
end // end of [parse_keyword_line]

(* ****** ****** *)

fun parse_identlst (): tokenlst = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKident _ => let
      val () = the_token_update ()
    in
      list_cons (tok, parse_identlst ())
    end // end of [TOKident]
  | _ => list_nil ()
end // end of [parse_identlst]

fn parse_prec_ident (): tokenopt = let
  val tok0 = the_token_get ()
in
  case+ tok0.token_node of
  | $Tok.TOKkeyword "%prec" => let
      val tok1 = the_token_update_get ()
    in
      case+ tok1.token_node of
      | $Tok.TOKident _ => let
          val () = the_token_update () in Some (tok1)
        end // end of [TOKident]
      | _ => begin
          prerr "The token at [";
          $Loc.prerr_location tok1.token_loc;
          prerr "] should be an identifier but it is not.";
          prerr_newline ();
          exit {tokenopt} (1)
        end // end of [_]
    end // end of [TOKkeyword "%prec"]
  | _ => None ()
end // end of [parse_prec_ident]

fn parse_extcode (): tokenopt = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKextcode _ => let
      val () = the_token_update () in Some (tok)
    end // end of [TOKextcode]
  | _ => None ()
end // end of [parse_extcode]

typedef rulerhs =
  @(tokenlst, tokenopt, tokenopt)

fn parse_rulerhs (): rulerhs = let
  val ids = parse_identlst ()
  val prec = parse_prec_ident ()
  val ext = parse_extcode ()
in
  @(ids, prec, ext)
end // end of [parse_rulerhs]

typedef rulerhslst = List (rulerhs)

fun parse_rulerhslst (): rulerhslst = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKkeychar '|' => let
      val () = the_token_update ()
      val rhs = parse_rulerhs ()
      val rhslst = parse_rulerhslst ()
    in
      list_cons (rhs, rhslst)
    end // end of [TOKkeychar '|']
  | $Tok.TOKkeychar ';' => let // ';' is optional
      val () = the_token_update () in list_nil ()
    end // end of [TOKkeychar ';']
(*
  | _ => begin
      prerr "The token at [";
      $Loc.prerr_location tok.token_loc;
      prerr "] should be either [;] but it is not.";
      prerr_newline ();
      exit {rulerhslst} (1)
    end // end of [_]
*)
  | _ => list_nil ()
end // end of [parse_rulerhslst]

typedef rule = @(token, rulerhslst)

fun parse_rule (): rule = let
  val tok0 = the_token_get ()
in
  case+ tok0.token_node of
  | $Tok.TOKident _ => let
      val tok1 = the_token_update_get ()
    in
      case+ tok1.token_node of
      | $Tok.TOKkeychar c
          when (c = ':' orelse c = '|') => let
          val () = the_token_update ()
          val rhs = parse_rulerhs ()
          val rhslst = parse_rulerhslst ()
        in
          (tok0, list_cons (rhs, rhslst))
        end // end of [TOKkeychar when ...]
      | _ => begin
          prerr "The token at [";
          $Loc.prerr_location tok1.token_loc;
          prerr "] should be either [:] or [|] but it is not.";
          prerr_newline ();
          exit (1)
        end // end of [_]
    end // end of [TOKident]
  | _ => begin
      prerr "The token at [";
      $Loc.prerr_location tok0.token_loc;
      prerr "] should an identifer but it is not.";
      prerr_newline ();
      exit (1)
    end // end of [_]
end // end of [parse_rule]

viewtypedef ruleopt_vt = Option_vt (rule)

fun parse_ruleopt (): ruleopt_vt = let
  val tok0 = the_token_get ()
in
  case+ tok0.token_node of
  | $Tok.TOKident _ => Some_vt (parse_rule ())
  | _ => None_vt ()
end // end of [parse_ruleopt]

(* ****** ****** *)

(*

fn parse_main () = loop () where {
  fun loop (): void = let
    val tok = atsyacc_lexer_token_get ()
    val () = begin
      $Loc.print tok.token_loc;
      print ": tok = "; $Tok.print_token tok;
      print_newline ()
    end // end of [val]
  in
    case+ tok.token_node of
    | $Tok.TOKeof () => () | _ => loop ()
  end // end of [loop]
} // end of [parse_main]

*)

extern fun parse_main (): void

local

val thePreambleRef = ref_make_elt<tokenopt> (None)
val thePostambleRef = ref_make_elt<tokenopt> (None)

in

implement parse_main () = let
  val () = the_token_update () // flush out a junk value
  val () = let // processing preamble
    val tok = the_token_get () in case+ tok.token_node of
    | $Tok.TOKpreamble _ => let
        val () = the_token_update () in !thePreambleRef := Some tok
      end // end of [TOKpreamble]
    | _ => ()
  end // end of [val]

  val () = loop () where { // processing keyword lines
    fun loop (): void = let
      var flag: int = 0
      val () = parse_keyword_line (flag)
    in
      if flag > 0 then loop () else ()
    end // end of [loop]
  } // end of [val]

  val () = parse_percperc ()

  val () = loop () where { // processing production rules
    fun loop (): void = let
      val rlopt = parse_ruleopt ()
    in
      case+ rlopt of
      | ~Some_vt (rl) => let
          // [rl] needs to be processed!!!
        in
          loop ()
        end // end of [Some_vt]
      | ~None_vt () => () // loop exists
    end // end of [loop]
  } // end of [val]

  val () = let // processing postamble
    val tok = the_token_get () in case+ tok.token_node of
    | $Tok.TOKeof () => ()
    | $Tok.TOKpercperc () => let
        val tok = the_token_update_get () in
        case+ tok.token_node of
        | $Tok.TOKpostamble _ => let
            val () = the_token_update () in !thePostambleRef := Some tok
          end // end of [TOKpostamble]
        | _ => ()
      end // end of [TOKpercperc]
    | _ => ()
  end // end of [val]
  
  val () = let
    val tok = the_token_get ()
  in
    case+ tok.token_node of
    | $Tok.TOKeof () => () | _ => begin
        prerr "The token at [";
        $Loc.prerr_location tok.token_loc;
        prerr "] should have been consumed but it is not.";
        prerr_newline ();
      end // end of [_]
  end // end of [val]
in
  // empty
end // end of [parse_main]

end // end of [local]

(* ****** ****** *)

staload LEXING = "libats/lex/lexing.sats"

implement parse_from_filename (filename) = let
(*
  val () = begin
    prerr "parse_from_filename: "; prerr filename; prerr_newline ()
  end // end of [val]
*)
  val file_mode_r = $extval (file_mode r, "\"r\"")
  val (pf_fil | p_fil) =
    $STDIO.fopen_exn (filename, file_mode_r)
  val (pf_infil | p_infil) =
    $LEXING.infile_make_file (pf_fil, file_mode_lte_r_r | p_fil)
  val (pf_lexbuf | lexbuf) =
    $LEXING.lexbuf_make_infile (pf_infil | p_infil)
  val () = $LEXING.lexing_lexbuf_set (pf_lexbuf | lexbuf)
  val ans = parse_main ()
in
  $LEXING.lexing_lexbuf_free (); ans
end // end of [parse_from_filename]

implement parse_from_stdin () = let
  val (pf_infil | p_infil) =
    $LEXING.infile_make_stdin ()
  val (pf_lexbuf | lexbuf) =
    $LEXING.lexbuf_make_infile (pf_infil | p_infil)
  val () = $LEXING.lexing_lexbuf_set (pf_lexbuf | lexbuf)
  val ans = parse_main ()
in
  $LEXING.lexing_lexbuf_free (); ans
end // end of [parse_from_stdin]

(* ****** ****** *)

(* end of [parser.dats] *)
