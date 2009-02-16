(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
**
*)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* functions for handling tokens *)

(* ****** ****** *)

typedef intchr = intBtw (~1, 1+UCHAR_MAX)
extern fun char_get (): intchr
extern fun char_get_mov (): intchr
extern fun char_mov (): void

(* ****** ****** *)

absprop ISLETTER (i: int, b: bool)

%{^

static ats_int_type
ats_bool_type int_isletter (ats_int_type i) {
  if ('a' <= i && i <= 'z') return ats_true_bool ;
  if ('A' <= i && i <= 'Z') return ats_true_bool ;
  if (i == '_') return ats_true_bool ;
  return ats_false_bool ;
}

%}

extern fun int_isletter {i:int}
  (i: int i): [b:bool] (ISLETTER (i, b) | bool b)
  = "int_isletter"

extern fun c1har_of_letter {i:int}
  (pf: ISLETTER (i, true) | i: int i): c1har
  = "atspre_char_of_int"

fn tokenize_ident (): string = let
  fun loop {n:nat} (cs: charlst_vt n, n: int n): string = let
    val i = char_get ()
    val (pf | b) = int_isletter (i)
  in
    if b then let
      val c = c1har_of_letter (pf | i) in char_mov (); loop (c :: cs, n+1)
    end else begin
      string_make_charlst_rev_int (cs, n)
    end // end of [if]
  end // end of [loop]
in
  loop (list_vt_nil (), 0)
end // end of [tokenize_ident]

(* ****** ****** *)

(* end of [token.dats] *)
