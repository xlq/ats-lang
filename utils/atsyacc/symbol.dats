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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
**
*)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "symbol.sats"

(* ****** ****** *)

staload H = "hashtable.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

#define NONASSOC	0
#define LEFTASSOC 	1
#define RIGHTASSOC 	2

local

typedef symbol = '{
  symbol_name= string
, symbol_index= int
// nonassoc: 0; leftassoc: 1; rightassoc: 2;
, symbol_assoc= int
}

assume symbol_t = symbol

val the_symcnt = ref_make_elt<int> (0)
val the_symtbl
  : $H.hashtbl_t (string, symbol_t) =
  $H.hashtbl_make (hash, eq) where {
  fn hash (x: string):<cloref> uint = string_hash_33 (x)
  fn eq (x1: string, x2: string):<cloref> bool = (x1 = x2)
} // end of [val]

fn symbol_make_name_index
  (name: string, index: int) = '{
  symbol_name= name, symbol_index= index, symbol_assoc= ~1
} // end of [symbol_make_string]

val NONTERM_START_INDEX = ref_make_elt<int> (0)

in // in of [local]

implement name_is_new (name) = let
  val ans = $H.hashtbl_search<string,symbol_t> (the_symtbl, name)
in
  case+ ans of ~None_vt () => true | ~Some_vt _ => false
end // end of [symbol_is_new]

implement symbol_make_name (name) = let
  val ans = $H.hashtbl_search<string,symbol_t> (the_symtbl, name)
in
  case+ ans of
  | ~Some_vt sym => sym | ~None_vt () => symbol_make_newname (name)
  // end of [case]
end // end of [symbol_make_name]

implement symbol_make_newname (name) = sym where {
  val index = !the_symcnt
  val () = !the_symcnt := index + 1
  val sym = symbol_make_name_index (name, index)
  val ans = begin
    $H.hashtbl_insert_err<string,symbol_t> (the_symtbl, name, sym)
  end // end of [val]
  val () = case+ ans of
    | ~None_vt () => () | ~Some_vt _ => begin
        prerr "Internal Error: symbol_make_string"; prerr_newline ();
        exit (1)
      end // end of [Some_vt]
  // end of [val]
} // end of [symbol_make_newname]

implement eq_symbol_symbol (x1, x2) = (x1.symbol_index = x2.symbol_index)
implement neq_symbol_symbol (x1, x2) = (x1.symbol_index <> x2.symbol_index)

implement compare_symbol_symbol (x1, x2) =
  compare (x1.symbol_index, x2.symbol_index)

implement symbol_is_term (x) =
  if x.symbol_index < !NONTERM_START_INDEX then true else false
implement symbol_is_nonterm (x) =
  if x.symbol_index >= !NONTERM_START_INDEX then true else false

extern typedef "symbol_t" = symbol

end // end of [local]

(* ****** ****** *)

%{$

ats_int_type
atsyacc_symbol_assoc_get (ats_ptr_type sym)
{
  return ((symbol_t)sym)->atslab_symbol_assoc ;
}

ats_void_type
atsyacc_symbol_assoc_set (ats_ptr_type sym, ats_int_type assoc)
{
  ((symbol_t)sym)->atslab_symbol_assoc = assoc ; return ;
}

%}

(* ****** ****** *)

(* end of [symbol.dats] *)
