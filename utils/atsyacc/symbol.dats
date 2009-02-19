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

staload "grammar.sats"

(* ****** ****** *)

staload "symbol.sats"

(* ****** ****** *)

staload H = "LIB/hashtable.dats"
staload S = "LIB/funset_avltree.dats"

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

%{^

typedef FILE ats_FILE_viewtype ;

%}

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
, symbol_nullable= bool
, symbol_frstset= symbolset_t
, symbol_fllwset= symbolset_t
, symbol_rulerhslst= rulerhslst
} // end of [symbol]
 
assume symbol_t = symbol

val the_symcnt = ref_make_elt<int> (0)
val the_symtbl =
  $H.hashtbl_make<string, symbol_t> (hash, eq) where {
  fn hash (x: string):<cloref> uint = string_hash_33 (x)
  fn eq (x1: string, x2: string):<cloref> bool = (x1 = x2)
} // end of [val]

fn symbol_make_name_index
  (name: string, index: int) = '{
  symbol_name= name
, symbol_index= index
, symbol_assoc= ~1 // default
, symbol_nullable= false // default
, symbol_frstset= symbolset_nil // default; it is to be computed
, symbol_fllwset= symbolset_nil // default; it is to be computed
, symbol_rulerhslst= list_nil ()
} // end of [symbol_make_string]

in // in of [local]

implement symbol_name_get (x) = x.symbol_name

implement symbol_find_name (name) =
  $H.hashtbl_search<string,symbol_t> (the_symtbl, name)
// end of [symbol_find_name]

implement name_is_new (name) = let
  val ans = $H.hashtbl_search<string,symbol_t> (the_symtbl, name)
in
  case+ ans of ~None_vt () => true | ~Some_vt _ => false
end // end of [name_is_new]

implement symbol_make_name (knd, name) = let
  val ans = $H.hashtbl_search<string,symbol_t> (the_symtbl, name)
in
  case+ ans of
  | ~Some_vt sym => sym | ~None_vt () => symbol_make_newname (knd, name)
  // end of [case]
end // end of [symbol_make_name]

implement symbol_make_newname (knd, name) = sym where {
  val n = !the_symcnt
  val () = !the_symcnt := n + 1
  val index = (case+ knd of
    | SYMKINDterm () => 2 * n | SYMKINDnonterm () => 2 * n + 1
  ) : int
  val sym = symbol_make_name_index (name, index)
  val () = case+ knd of
    | SYMKINDterm () => () where {
        val () = symbol_frstset_set (sym, symbolset_sing sym)
      } // end of [SYMKINDterm]
    | SYMKINDnonterm () => () // frstset is to be computed later
  // end of [val]
  val ans = begin
    $H.hashtbl_insert_err<string,symbol_t> (the_symtbl, name, sym)
  end // end of [val]
  val () = case+ ans of
    | ~None_vt () => () | ~Some_vt _ => begin
        prerr "Internal Error: symbol_make_newname"; prerr_newline ();
        exit (1)
      end // end of [Some_vt]
  // end of [val]
} // end of [symbol_make_newname]

//

implement the_end_symbol =
  symbol_make_newname (SYMKINDterm, "$end")

implement the_accept_symbol =
  symbol_make_newname (SYMKINDnonterm, "$accept")

//

implement eq_symbol_symbol (x1, x2) = (x1.symbol_index = x2.symbol_index)
implement neq_symbol_symbol (x1, x2) = (x1.symbol_index <> x2.symbol_index)

implement compare_symbol_symbol (x1, x2) =
  compare (x1.symbol_index, x2.symbol_index)

(* ****** ****** *)

implement fprint_symbol (pf_mod | out, x) = let
  val () = fprint1_string (pf_mod | out, x.symbol_name)
(*  
  val () = fprintf (pf_mod | out, "(%i)", @(x.symbol_index))
*)
in
  // empty
end // end of [fprint_symbol]

implement print_symbol (x) = print_mac (fprint_symbol, x)
implement prerr_symbol (x) = prerr_mac (fprint_symbol, x)

(* ****** ****** *)

implement symbol_is_term (x) =
  if x.symbol_index mod 2 = 0 then true else false

implement symbol_is_nonterm (x) =
  if x.symbol_index mod 2 = 1 then true else false

(* ****** ****** *)

implement symbol_total_get () = !the_symcnt

implement symbol_term_total_get () = n where {
  var n: int = 0
  viewdef V = int @ n
  var !p_clo = @lam (pf: !V | _: string, x: &symbol_t): void =>
    if symbol_is_term x then (n := n + 1)
  val () = $H.hashtbl_foreach_clo<string,symbol_t> {V} (view@ n | the_symtbl, !p_clo)
} // end of [symbol_term_total_get]

implement symbol_nonterm_total_get () = n where {
  var n: int = 0
  viewdef V = int @ n
  var !p_clo = @lam (pf: !V | _: string, x: &symbol_t): void =>
    if symbol_is_nonterm x then (n := n + 1)
  val () = $H.hashtbl_foreach_clo<string,symbol_t> {V} (view@ n | the_symtbl, !p_clo)
} // end of [symbol_term_total_get]

(* ****** ****** *)

extern typedef "symbol_t" = symbol

(* ****** ****** *)

end // end of [local]

(* ****** ****** *)

local

assume symbolset_t = $S.set_t (symbol_t)

val _cmp = lam (x1: symbol_t, x2: symbol_t)
  : Sgn =<cloref> compare_symbol_symbol (x1, x2)

in // in of [local]

implement symbolset_nil = $S.funset_empty<> ()
implement symbolset_sing (x) = $S.funset_singleton<symbol_t> (x)

implement $S.compare_elt_elt<symbol_t>
  (x1, x2, cmp) = compare_symbol_symbol (x1, x2)

implement symbolset_is_nil (xs) = $S.funset_is_empty (xs)
implement symbolset_isnot_nil (xs) = $S.funset_isnot_empty (xs)

implement symbolset_ismem (xs, x) = $S.funset_member (xs, x, _cmp)

//

implement symbolset_add (xs, x) =
  $S.funset_insert<symbol_t> (xs, x, _cmp)

implement symbolset_union (xs, ys) =
  $S.funset_union<symbol_t> (xs, ys, _cmp)

//

implement symbolset_add_flag (xs, x, flag) =
  if symbolset_ismem (xs, x) then xs else let
    val xs = $S.funset_insert<symbol_t> (xs, x, _cmp) in flag := flag+1; xs
  end // end of [if]
// end of [symbolset_add_flag]

implement symbolset_union_flag (xs, ys, flag) = let
  var res: symbolset_t = xs
  stavar l_flag: addr
  val p_flag : ptr l_flag = &flag
  viewdef V = (symbolset_t @ res, int @ l_flag)
  var !p_clo = @lam (pf: !V | y: symbol_t): void => () where {
    prval (pf1, pf2) = pf
    val () = res := symbolset_add_flag (res, y, !p_flag)
    prval () = pf := (pf1, pf2)
  } // end of [var]
  prval pf = (view@ res, view@ flag)
  val () = $S.funset_foreach_clo<symbol_t> {V} (pf | ys, !p_clo)
  prval () = view@ res := pf.0 and () = view@ flag := pf.1
in
  res
end // end of [symbolset_union]

//

implement fprint_symbolset {m} (pf_mod | out, xs) = let
  var i: int = 0
  stavar l_out: addr
  val p_out: ptr l_out = &out
  viewdef V = (int @ i, FILE m @ l_out)
  var !p_clo = @lam (pf: !V | x: symbol_t): void => let
    prval (pf1, pf2) = pf
    val () = if i > 0 then fprint1_string (pf_mod | out, ", ")
    val () = i := i + 1
    val () = fprint_symbol (pf_mod | out, x)
    prval () = pf := (pf1, pf2)
  in
    // empty
  end // end of [var]
  prval pf = (view@ i, view@ out)
  val () = $S.funset_foreach_clo<symbol_t> {V} (pf | xs, !p_clo)
  prval () = view@ i := pf.0 and () = view@ out := pf.1
in
  // empty
end // end of [fprint_symbolset]

implement print_symbolset (xs) = print_mac (fprint_symbolset, xs)
implement prerr_symbolset (xs) = prerr_mac (fprint_symbolset, xs)

end // end of [local]

(* ****** ****** *)

%{$

ats_int_type
atsyacc_symbol_assoc_get (ats_ptr_type sym) {
  return ((symbol_t)sym)->atslab_symbol_assoc ;
}

ats_void_type
atsyacc_symbol_assoc_set
  (ats_ptr_type sym, ats_int_type assoc) {
  ((symbol_t)sym)->atslab_symbol_assoc = assoc ; return ;
}

/* ****** ****** */

ats_bool_type
atsyacc_symbol_nullable_get (ats_ptr_type sym) {
  return ((symbol_t)sym)->atslab_symbol_nullable ;
}

ats_void_type
atsyacc_symbol_nullable_set
  (ats_ptr_type sym, ats_bool_type nullable) {
  ((symbol_t)sym)->atslab_symbol_nullable = nullable ; return ;
}

/* ****** ****** */

ats_ptr_type // symbolset
atsyacc_symbol_frstset_get (ats_ptr_type sym) {
  return ((symbol_t)sym)->atslab_symbol_frstset ;
}

ats_void_type
atsyacc_symbol_frstset_set
  (ats_ptr_type sym, ats_ptr_type frstset) {
  ((symbol_t)sym)->atslab_symbol_frstset = frstset ; return ;
}

/* ****** ****** */

ats_ptr_type // symbolset
atsyacc_symbol_fllwset_get (ats_ptr_type sym) {
  return ((symbol_t)sym)->atslab_symbol_fllwset ;
}

ats_void_type
atsyacc_symbol_fllwset_set
  (ats_ptr_type sym, ats_ptr_type fllwset) {
  ((symbol_t)sym)->atslab_symbol_fllwset = fllwset ; return ;
}

/* ****** ****** */

ats_ptr_type // symbolset
atsyacc_symbol_rulerhslst_get (ats_ptr_type sym) {
  return ((symbol_t)sym)->atslab_symbol_rulerhslst ;
}

ats_void_type
atsyacc_symbol_rulerhslst_set
  (ats_ptr_type sym, ats_ptr_type rulerhslst) {
  ((symbol_t)sym)->atslab_symbol_rulerhslst = rulerhslst ; return ;
}

%}

(* ****** ****** *)

(* end of [symbol.dats] *)
