(*
**
** For documenting the grammar of ATS/Anairiats
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Sylvain Nahas (sylvain.nahas AT googlemail DOT com)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

dynload "atsgrammar_symbol.dats"
dynload "atsgrammar_grmrule.dats"

(* ****** ****** *)

local
//
assume symbol_open_v (s:int) = unit_v
//
in // in of [local]
//
implement
symbol_open (sym) = (unit_v () | ())
//
implement
symbol_close
  (pf | sym) = let
  prval unit_v () = pf
  val grs1 = theGrmrulelst_get ()
  val grs2 = symbol_get_grmrulelst (sym)
  val grs = revapp (grs1, grs2) where {
    fun revapp (
      grs1: grmrulelst_vt, grs2: grmrulelst
    ) : grmrulelst = case+ grs1 of
      | ~list_vt_cons (gr, grs1) => revapp (grs1, list_cons (gr, grs2))
      | ~list_vt_nil () => grs2
    // end of [revapp]
  } // end of [val]
in
  symbol_set_grmrulelst (sym, grs)
end // end of [symbol_close]
//
end // end of [local]

(* ****** ****** *)

fn symbol_make
  (name: string) = x where {
  val x = symbol_make (name)
  val () = (
    print ("symbol_make: x = "); print x; print_newline ()
  ) // end of [val]
} // end of [symbol_make]

fn symbol_make_nt
  (name: string) = x where {
  val x = symbol_make_nt (name)
  val () = (
    print ("symbol_make_nt: x = "); print x; print_newline ()
  ) // end of [val]
} // end of [symbol_make_nt]

(* ****** ****** *)
//
val LITERAL_char = symbol_make "LITERAL_char"
val LITERAL_extcode = symbol_make "LITERAL_extcode"
val LITERAL_float = symbol_make "LITERAL_float"
val LITERAL_floatsp = symbol_make "LITERAL_floatsp"
val LITERAL_int = symbol_make "LITERAL_int"
val LITERAL_intsp = symbol_make "LITERAL_intsp"
val LITERAL_string = symbol_make "LITERAL_string"
//
val IDENTIFIER_alp = symbol_make "IDENTIFIER_alp"
val () = symbol_set_fullname
  (IDENTIFIER_alp, "ALPHANUMERIC_IDENTIFIER")
//
val IDENTIFIER_sym = symbol_make "IDENTIFIER_sym"
val () = symbol_set_fullname (IDENTIFIER_sym, "SYMBOLIC_IDENTIFIER")
//
val IDENTIFIER_arr = symbol_make "IDENTIFIER_arr"
val () = symbol_set_fullname (IDENTIFIER_arr, "ARRAY_IDENTIFIER")
val IDENTIFIER_tmp = symbol_make "IDENTIFIER_tmp"
val () = symbol_set_fullname (IDENTIFIER_tmp, "TEMPLATE_IDENTIFIER")
val IDENTIFIER_ext = symbol_make "IDENTIFIER_ext"
val () = symbol_set_fullname (IDENTIFIER_ext, "EXTERNAL_IDENTIFIER")
//
val IDENTIFIER_dlr = symbol_make "IDENTIFIER_dlr"
val IDENTIFIER_srp = symbol_make "IDENTIFIER_srp"
//
(* ****** ****** *)
//
val EQ = symbol_make ("EQ")
val () = symbol_set_fullname (EQ, "\"=\"")
//
val GT = symbol_make ("GT")
val () = symbol_set_fullname (GT, "\">\"")
//
val LT = symbol_make ("LT")
val () = symbol_set_fullname (LT, "\"<\"")
//
(* ****** ****** *)
//
val ABSPROP = symbol_make "ABSPROP"
val () = symbol_set_fullname (ABSPROP, "\"absprop\"")
//
val ABSTYPE = symbol_make "ABSTYPE"
val () = symbol_set_fullname (ABSTYPE, "\"abstype\"")
//
val ABST0YPE = symbol_make "ABST@YPE"
val () = symbol_set_fullname (ABST0YPE, "\"abst@ype\"")
//
val ABSVIEW = symbol_make "ABSVIEW"
val () = symbol_set_fullname (ABSVIEW, "\"absview\"")
//
val ABSVIEWTYPE = symbol_make "ABSVIEWTYPE"
val () = symbol_set_fullname (ABSVIEWTYPE, "\"absviewtype\"")
//
val ABSVIEWT0YPE = symbol_make "ABSVIEWT@YPE"
val () = symbol_set_fullname (ABSVIEWT0YPE, "\"absviewt@ype\"")
//
val AND = symbol_make "AND"
val () = symbol_set_fullname (AND, "\"and\"")
//
val AS = symbol_make "AS"
val () = symbol_set_fullname (AS, "\"as\"")
//
val ASSUME = symbol_make "ASSUME"
val () = symbol_set_fullname (ASSUME, "\"assume\"")
//
val CASTFN = symbol_make "CASTFN"
val () = symbol_set_fullname (CASTFN, "\"castfn\"")
//
val FUN = symbol_make "FUN"
val () = symbol_set_fullname (FUN, "\"fun\"")
//
val PRAXI = symbol_make "PRAXI"
val () = symbol_set_fullname (PRAXI, "\"praxi\"")
//
val PRFUN = symbol_make "PRFUN"
val () = symbol_set_fullname (PRFUN, "\"prfun\"")
//
val PRVAL = symbol_make "PRVAL"
val () = symbol_set_fullname (PRVAL, "\"prval\"")
//
val VAL = symbol_make "VAL"
val () = symbol_set_fullname (VAL, "\"val\"")
//
(* ****** ****** *)

val abskind = symbol_make_nt "abskind"
val dcstkind = symbol_make_nt "dcstkind"

(* ****** ****** *)

val i0de = symbol_make_nt "i0de"
val i0deseq = symbol_make_nt "i0deseq"

(* ****** ****** *)

val d0ec_sta = symbol_make_nt "d0ec_sta"
val d0ecseq_sta = symbol_make_nt "d0ecseq_sta"
val d0ec_dyn = symbol_make_nt "d0ec_dyn"
val d0ecseq_dyn = symbol_make_nt "d0ecseq_dyn"
val d0ecseq_dyn_rev = symbol_make_nt "d0ecseq_dyn_rev"

(* ****** ****** *)

(*
abskind
  : ABSPROP                             { $$ = abskind_prop () ; }
  | ABSTYPE                             { $$ = abskind_type () ; }
  | ABST0YPE                            { $$ = abskind_t0ype () ; }
  | ABSVIEW                             { $$ = abskind_view () ; }
  | ABSVIEWTYPE                         { $$ = abskind_viewtype () ; }
  | ABSVIEWT0YPE                        { $$ = abskind_viewt0ype () ; }
  ;
*)
fun abskind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (abskind)
//
val () = grmrule_append (ABSPROP)
val () = grmrule_append (ABSTYPE)
val () = grmrule_append (ABST0YPE)
val () = grmrule_append (ABSVIEW)
val () = grmrule_append (ABSVIEWTYPE)
val () = grmrule_append (ABSVIEWT0YPE)
//
val () = symbol_close (pf | abskind)
} // end of [abskind_proc]

(* ****** ****** *)

(*
dcstkind
  : FUN                                 { $$ = dcstkind_fun () ; }
  | VAL                                 { $$ = dcstkind_val () ; }
  | PRAXI                               { $$ = dcstkind_praxi () ; }
  | PRFUN                               { $$ = dcstkind_prfun () ; }
  | PRVAL                               { $$ = dcstkind_prval () ; }
  | CASTFN                              { $$ = dcstkind_castfn () ; }
;
*)
fun dcstkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (dcstkind)
//
val () = grmrule_append (FUN)
val () = grmrule_append (VAL)
val () = grmrule_append (PRAXI)
val () = grmrule_append (PRFUN)
val () = grmrule_append (PRVAL)
val () = grmrule_append (CASTFN)
//
val () = symbol_close (pf | dcstkind)
} // end of [dcstkind_proc]

(* ****** ****** *)

fun i0deseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (i0deseq)
//
val () = grmrule_append ()
val () = grmrule_append ($lst_t {symbol} (tupz! i0de i0deseq))
//
val () = symbol_close (pf | i0deseq)
//
} // end of [i0deseq_proc]

(* ****** ****** *)

(*
d0ecseq_dyn_rev /* tail-recursive */
  : /* empty */                         { $$ = d0ecllst_nil() ; }
  | d0ecseq_dyn_rev d0ec_dyn semicolonseq
                                        { $$ = d0ecllst_cons($1, $2) ; }
;
*)
fun d0ecseq_dyn_rev_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecseq_dyn_rev)
//
val () = grmrule_append ()
val () = grmrule_append ($lst_t {symbol} (tupz! d0ecseq_dyn_rev d0ec_dyn))
//
val () = symbol_close (pf | d0ecseq_dyn_rev)
//
} // end of [d0ecseq_dyn_proc]

(*
d0ecseq_dyn
  : d0ecseq_dyn_rev                     { $$ = d0ecllst_reverse($1) ; }
;
*)
fun d0ecseq_dyn_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecseq_dyn)
//
val () = grmrule_append (d0ecseq_dyn_rev)
//
val () = symbol_close (pf | d0ecseq_dyn)
//
} // end of [d0ecseq_dyn_proc]

(* ****** ****** *)

extern fun atsgrammar_main (): void

(* ****** ****** *)

implement
atsgrammar_main
  () = () where {
  val () = abskind_proc ()
  val () = dcstkind_proc ()
  val () = i0deseq_proc ()
  val () = d0ecseq_dyn_rev_proc () // reversed dynamic declaration sequence
  val () = d0ecseq_dyn_proc ()
} // end of [atsgrammar_main]

(* ****** ****** *)

implement main () = ()

(* ****** ****** *)

(* end of [atsgrammar_main.dats] *)
