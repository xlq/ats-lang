(*
** Course: Concepts of Programming Languages (BU CAS CS 320)
** Semester: Summer I, 2009
** Instructor: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June, 2009
//

(* ****** ****** *)

staload "symbol.sats"

(* ****** ****** *)

staload H = "HASHTABLE/hashtable.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

local

assume symbol_t = '{
  symbol_name= string, symbol_index= int
}

val the_symtbl =
  $H.hashtbl_make<string, symbol_t> (hash, eqfn) where {
  val hash = lam (x: string): uint =<cloref> string_hash_33 (x)
  val eqfn = lam (x1: string, x2: string): bool =<cloref> (x1 = x2)
} // end of [val]

val the_symcnt = ref_make_elt<int> (0)

in // in of [local]

fn symbol_make_name_index
  (name: string, index: int): symbol_t = '{
  symbol_name= name
, symbol_index= index
} // end of [symbol_make_name_index]

implement symbol_make_name (name: string) = let
  val ans = $H.hashtbl_search (the_symtbl, name)
in
  case+ ans of
  | ~Some_vt sym => sym | ~None_vt _ => let
      val n = !the_symcnt; val () = !the_symcnt := n+1
      val sym = symbol_make_name_index (name, n)
      val ans = $H.hashtbl_insert_err<string,symbol_t>
        (the_symtbl, name, sym) // end of [hashtbl_insert_err]
      val () = begin
        case+ ans of ~Some_vt _ => () | ~None_vt _ => ()
      end // end of [val]
    in
      sym
    end // end of [None_vt]
end // end of [symbol_make]

implement symbol_name_get (x) = x.symbol_name

//

implement fprint_symbol (out, x) = fprint (out, x.symbol_name)

(*

implement fprint_symbol (out, x) =
  fprintf (out, "%s(%i)", @(x.symbol_name, x.symbol_index))

*)

implement print_symbol (x) = fprint_symbol (stdout_ref, x)
implement prerr_symbol (x) = fprint_symbol (stderr_ref, x)

//

implement eq_symbol_symbol
  (x1, x2) = x1.symbol_index = x2.symbol_index
// end of [eq_symbol_symbol]

implement neq_symbol_symbol
  (x1, x2) = x1.symbol_index <> x2.symbol_index
// end of [eq_symbol_symbol]

implement compare_symbol_symbol (x1, x2) =
  compare (x1.symbol_index, x2.symbol_index)
// end of [eq_symbol_symbol]

end // end of [local]

(* ****** ****** *)

implement symbol_BOOL = symbol_make_name "bool"
implement symbol_INT = symbol_make_name "int"
implement symbol_STRING = symbol_make_name "string"
implement symbol_UNIT = symbol_make_name "unit"

(* ****** ****** *)

implement symbol_PLUS = symbol_make_name "+"
implement symbol_MINUS = symbol_make_name "-"
implement symbol_TIMES = symbol_make_name "*"
implement symbol_SLASH = symbol_make_name "/"
implement symbol_UMINUS = symbol_make_name "~"

implement symbol_GT = symbol_make_name ">"
implement symbol_GTE = symbol_make_name ">="
implement symbol_LT = symbol_make_name "<"
implement symbol_LTE = symbol_make_name "<="
implement symbol_EQ = symbol_make_name "="
implement symbol_NEQ = symbol_make_name "<>"

implement symbol_PRINT = symbol_make_name "print"
implement symbol_PRINT_INT = symbol_make_name "print_int"

(* ****** ****** *)

local

typedef sym = symbol_t
assume symtbl_t (a:t@ype) = $H.hashtbl_t (symbol_t, a)

in // in of [local]

implement{itm} symtbl_make () = let
  val hash = lam (x: sym) =<cloref> string_hash_33 (symbol_name_get x)
  val eq = lam (x1: sym, x2: sym) =<cloref> x1 = x2
in
  $H.hashtbl_make<sym,itm> (hash, eq)
end // end of [symtbl_make]

implement{itm} symtbl_lookup (tbl, sym) = $H.hashtbl_search<sym,itm> (tbl, sym)

implement{itm} symtbl_insert (tbl, sym, itm) = let
  val ans = $H.hashtbl_insert_err<sym,itm> (tbl, sym, itm)
in
  case+ ans of
  | ~Some_vt _ => let
      val () = begin
        prerr "exit(TIGER): [symtbl_insert] failed."; prerr_newline ()
      end // end of [val]
    in
      exit {void} (1)
    end // end of [Some_vt]
  | ~None_vt () => ()
end // end of [symbol_insert]

end // end of [local]

(* ****** ****** *)

(* end of [symbol.dats] *)
