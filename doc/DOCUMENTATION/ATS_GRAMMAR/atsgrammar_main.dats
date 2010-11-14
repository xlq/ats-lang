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
//
dynload "atsgrammar_tyname.dats"
dynload "atsgrammar_symbol.dats"
dynload "atsgrammar_grmrule.dats"
//
dynload "atsgrammar_emit_yats.dats"
dynload "atsgrammar_emit_desc.dats"
//
(* ****** ****** *)

val t0kn_tyname = tyname_make_string "t0kn"
val c0har_tyname = tyname_make_string "c0har"
val e0xtcode_tyname = tyname_make_string "e0xtcode"
val f0loat_tyname = tyname_make_string "f0loat"
val f0loatsp_tyname = tyname_make_string "f0loatsp"
val i0nt_tyname = tyname_make_string "i0nt"
val i0ntsp_tyname = tyname_make_string "i0ntsp"
val s0tring_tyname = tyname_make_string "s0tring"
val i0de_tyname = tyname_make_string "i0de"

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
  (name: string): symbol = x where {
  val x = symbol_make (name)
  val () = theSymlst_add (x)
(*
  val () = (
    print ("symbol_make: x = "); print x; print_newline ()
  ) // end of [val]
*)
} // end of [symbol_make]

fn symbol_make_nt
  (name: string): symbol = x where {
  val x = symbol_make_nt (name)
  val () = theSymlst_add (x)
(*
  val () = (
    print ("symbol_make_nt: x = "); print x; print_newline ()
  ) // end of [val]
*)
} // end of [symbol_make_nt]

(* ****** ****** *)
//
val TOKEN_eof = symbol_make "TOKEN_eof"
val () = symbol_set_tyname (TOKEN_eof, t0kn_tyname)
//
val ISSTATIC = symbol_make "ISSTATIC"
val () = symbol_set_tyname (ISSTATIC, t0kn_tyname)
val ISDYNAMIC = symbol_make "ISDYNAMIC"
val () = symbol_set_tyname (ISDYNAMIC, t0kn_tyname)
//
(* ****** ****** *)
//
val LITERAL_char = symbol_make "LITERAL_char"
val () = symbol_set_tyname (LITERAL_char, c0har_tyname)
//
val LITERAL_extcode = symbol_make "LITERAL_extcode"
val () = symbol_set_tyname (LITERAL_extcode, e0xtcode_tyname)
//
val LITERAL_float = symbol_make "LITERAL_float"
val () = symbol_set_tyname (LITERAL_float, f0loat_tyname)
val LITERAL_floatsp = symbol_make "LITERAL_floatsp"
val () = symbol_set_tyname (LITERAL_floatsp, f0loatsp_tyname)
//
val LITERAL_int = symbol_make "LITERAL_int"
val () = symbol_set_tyname (LITERAL_int, i0nt_tyname)
val LITERAL_intsp = symbol_make "LITERAL_intsp"
val () = symbol_set_tyname (LITERAL_intsp, i0ntsp_tyname)
//
val LITERAL_string = symbol_make "LITERAL_string"
val () = symbol_set_tyname (LITERAL_string, s0tring_tyname)
//
val IDENTIFIER_alp = symbol_make "IDENTIFIER_alp"
val () = symbol_set_fullname
  (IDENTIFIER_alp, "ALNUMRIC_IDENTIFIER")
val () = symbol_set_tyname (IDENTIFIER_alp, i0de_tyname)
//
val IDENTIFIER_sym = symbol_make "IDENTIFIER_sym"
val () = symbol_set_fullname (IDENTIFIER_sym, "SYMBOLIC_IDENTIFIER")
val () = symbol_set_tyname (IDENTIFIER_sym, i0de_tyname)
//
val IDENTIFIER_arr = symbol_make "IDENTIFIER_arr"
val () = symbol_set_fullname (IDENTIFIER_arr, "ARRAY_IDENTIFIER")
val () = symbol_set_tyname (IDENTIFIER_arr, i0de_tyname)
//
val IDENTIFIER_tmp = symbol_make "IDENTIFIER_tmp"
val () = symbol_set_fullname (IDENTIFIER_tmp, "TEMPLATE_IDENTIFIER")
val () = symbol_set_tyname (IDENTIFIER_tmp, i0de_tyname)
//
val IDENTIFIER_ext = symbol_make "IDENTIFIER_ext"
val () = symbol_set_fullname (IDENTIFIER_ext, "EXTERNAL_IDENTIFIER")
val () = symbol_set_tyname (IDENTIFIER_ext, i0de_tyname)
//
val IDENTIFIER_dlr = symbol_make "IDENTIFIER_dlr"
val () = symbol_set_tyname (IDENTIFIER_dlr, i0de_tyname)
//
val IDENTIFIER_srp = symbol_make "IDENTIFIER_srp"
val () = symbol_set_tyname (IDENTIFIER_srp, i0de_tyname)
//
(* ****** ****** *)
//
val ABSPROP = symbol_make "ABSPROP"
val () = symbol_set_fullname (ABSPROP, "\"absprop\"")
val () = symbol_set_tyname (ABSPROP, t0kn_tyname)
//
val ABSTYPE = symbol_make "ABSTYPE"
val () = symbol_set_fullname (ABSTYPE, "\"abstype\"")
val () = symbol_set_tyname (ABSTYPE, t0kn_tyname)
//
val ABST0YPE = symbol_make "ABST0YPE"
val () = symbol_set_fullname (ABST0YPE, "\"abst@ype\"")
val () = symbol_set_tyname (ABST0YPE, t0kn_tyname)
//
val ABSVIEW = symbol_make "ABSVIEW"
val () = symbol_set_fullname (ABSVIEW, "\"absview\"")
val () = symbol_set_tyname (ABSVIEW, t0kn_tyname)
//
val ABSVIEWTYPE = symbol_make "ABSVIEWTYPE"
val () = symbol_set_fullname (ABSVIEWTYPE, "\"absviewtype\"")
val () = symbol_set_tyname (ABSVIEWTYPE, t0kn_tyname)
//
val ABSVIEWT0YPE = symbol_make "ABSVIEWT0YPE"
val () = symbol_set_fullname (ABSVIEWT0YPE, "\"absviewt@ype\"")
val () = symbol_set_tyname (ABSVIEWT0YPE, t0kn_tyname)
//
val AND = symbol_make "AND"
val () = symbol_set_fullname (AND, "\"and\"")
val () = symbol_set_tyname (AND, t0kn_tyname)
//
val AS = symbol_make "AS"
val () = symbol_set_fullname (AS, "\"as\"")
val () = symbol_set_tyname (AS, t0kn_tyname)
//
val ASSUME = symbol_make "ASSUME"
val () = symbol_set_fullname (ASSUME, "\"assume\"")
val () = symbol_set_tyname (ASSUME, t0kn_tyname)
//
val ATLAM = symbol_make "ATLAM"
val () = symbol_set_fullname (ATLAM, "\"@lam\"")
val () = symbol_set_tyname (ATLAM, t0kn_tyname)
val ATLLAM = symbol_make "ATLLAM"
val () = symbol_set_fullname (ATLLAM, "\"@llam\"")
val () = symbol_set_tyname (ATLLAM, t0kn_tyname)
val ATFIX = symbol_make "ATFIX"
val () = symbol_set_fullname (ATFIX, "\"@fix\"")
val () = symbol_set_tyname (ATFIX, t0kn_tyname)
//
val BEGIN = symbol_make "BEGIN"
val () = symbol_set_fullname (BEGIN, "\"begin\"")
val () = symbol_set_tyname (BEGIN, t0kn_tyname)
//
val BREAK = symbol_make "BREAK"
val () = symbol_set_fullname (BREAK, "\"break\"")
val () = symbol_set_tyname (BREAK, t0kn_tyname)
//
val CASE = symbol_make "CASE"
val () = symbol_set_fullname (CASE, "\"case\"")
val () = symbol_set_tyname (CASE, t0kn_tyname)
val CASEMINUS = symbol_make "CASEMINUS"
val () = symbol_set_fullname (CASEMINUS, "\"case-\"")
val () = symbol_set_tyname (CASEMINUS, t0kn_tyname)
val CASEPLUS = symbol_make "CASEPLUS"
val () = symbol_set_fullname (CASEPLUS, "\"case+\"")
val () = symbol_set_tyname (CASEPLUS, t0kn_tyname)
//
val CASTFN = symbol_make "CASTFN"
val () = symbol_set_fullname (CASTFN, "\"castfn\"")
val () = symbol_set_tyname (CASTFN, t0kn_tyname)
//
val CLASSDEC = symbol_make "CLASSDEC"
val () = symbol_set_fullname (CLASSDEC, "\"classdec\"")
val () = symbol_set_tyname (CLASSDEC, t0kn_tyname)
//
val CONTINUE = symbol_make "CONTINUE"
val () = symbol_set_fullname (CONTINUE, "\"continue\"")
val () = symbol_set_tyname (CONTINUE, t0kn_tyname)
//
val DATASORT = symbol_make "DATASORT"
val () = symbol_set_fullname (DATASORT, "\"datasort\"")
val () = symbol_set_tyname (DATASORT, t0kn_tyname)
val DATAPARASORT = symbol_make "DATAPARASORT"
val () = symbol_set_fullname (DATAPARASORT, "\"dataparasort\"")
val () = symbol_set_tyname (DATAPARASORT, t0kn_tyname)
//
val DATAPROP = symbol_make "DATAPROP"
val () = symbol_set_fullname (DATAPROP, "\"dataprop\"")
val () = symbol_set_tyname (DATAPROP, t0kn_tyname)
val DATATYPE = symbol_make "DATATYPE"
val () = symbol_set_fullname (DATATYPE, "\"datatype\"")
val () = symbol_set_tyname (DATATYPE, t0kn_tyname)
val DATAVIEW = symbol_make "DATAVIEW"
val () = symbol_set_fullname (DATAVIEW, "\"dataview\"")
val () = symbol_set_tyname (DATAVIEW, t0kn_tyname)
val DATAVIEWTYPE = symbol_make "DATAVIEWTYPE"
val () = symbol_set_fullname (DATAVIEWTYPE, "\"dataviewtype\"")
val () = symbol_set_tyname (DATAVIEWTYPE, t0kn_tyname)
//
val DO = symbol_make "DO"
val () = symbol_set_fullname (DO, "\"do\"")
val () = symbol_set_tyname (DO, t0kn_tyname)
//
val DYN = symbol_make "DYN"
val () = symbol_set_fullname (DYN, "\"dyn\"")
val () = symbol_set_tyname (DYN, t0kn_tyname)
//
val DYNLOAD = symbol_make "DYNLOAD"
val () = symbol_set_fullname (DYNLOAD, "\"dynload\"")
val () = symbol_set_tyname (DYNLOAD, t0kn_tyname)
//
val ELSE = symbol_make "ELSE"
val () = symbol_set_fullname (ELSE, "\"else\"")
val () = symbol_set_tyname (ELSE, t0kn_tyname)
//
val END = symbol_make "END"
val () = symbol_set_fullname (END, "\"end\"")
val () = symbol_set_tyname (END, t0kn_tyname)
//
val EXCEPTION = symbol_make "EXCEPTION"
val () = symbol_set_fullname (EXCEPTION, "\"exception\"")
val () = symbol_set_tyname (EXCEPTION, t0kn_tyname)
//
val EXTERN = symbol_make "EXTERN"
val () = symbol_set_fullname (EXTERN, "\"extern\"")
val () = symbol_set_tyname (EXTERN, t0kn_tyname)
//
val FIX = symbol_make "FIX"
val () = symbol_set_fullname (FIX, "\"fix\"")
val () = symbol_set_tyname (FIX, t0kn_tyname)
//
val FN = symbol_make "FN"
val () = symbol_set_fullname (FN, "\"fn\"")
val () = symbol_set_tyname (FN, t0kn_tyname)
val FNSTAR = symbol_make "FNSTAR"
val () = symbol_set_fullname (FNSTAR, "\"fn*\"")
val () = symbol_set_tyname (FNSTAR, t0kn_tyname)
//
val FOR = symbol_make "FOR"
val () = symbol_set_fullname (FOR, "\"for\"")
val () = symbol_set_tyname (FOR, t0kn_tyname)
val FORSTAR = symbol_make "FORSTAR"
val () = symbol_set_fullname (FORSTAR, "\"for*\"")
val () = symbol_set_tyname (FORSTAR, t0kn_tyname)
//
val FUN = symbol_make "FUN"
val () = symbol_set_fullname (FUN, "\"fun\"")
val () = symbol_set_tyname (FUN, t0kn_tyname)
//
val IF = symbol_make "IF"
val () = symbol_set_fullname (IF, "\"if\"")
val () = symbol_set_tyname (IF, t0kn_tyname)
//
val IMPLEMENT = symbol_make "IMPLEMENT"
val () = symbol_set_fullname (IMPLEMENT, "\"implement\"")
val () = symbol_set_tyname (IMPLEMENT, t0kn_tyname)
//
val IN = symbol_make "IN"
val () = symbol_set_fullname (IN, "\"in\"")
val () = symbol_set_tyname (IN, t0kn_tyname)
//
val INFIX = symbol_make "INFIX"
val () = symbol_set_fullname (INFIX, "\"infix\"")
val () = symbol_set_tyname (INFIX, t0kn_tyname)
val INFIXL = symbol_make "INFIXL"
val () = symbol_set_fullname (INFIXL, "\"infixl\"")
val () = symbol_set_tyname (INFIXL, t0kn_tyname)
val INFIXR = symbol_make "INFIXR"
val () = symbol_set_fullname (INFIXR, "\"infixr\"")
val () = symbol_set_tyname (INFIXR, t0kn_tyname)
//
val LAM = symbol_make "LAM"
val () = symbol_set_fullname (LAM, "\"lam\"")
val () = symbol_set_tyname (LAM, t0kn_tyname)
//
val LET = symbol_make "LET"
val () = symbol_set_fullname (LET, "\"let\"")
val () = symbol_set_tyname (LET, t0kn_tyname)
//
val LLAM = symbol_make "LLAM"
val () = symbol_set_fullname (LLAM, "\"llam\"")
val () = symbol_set_tyname (LLAM, t0kn_tyname)
//
val LOCAL = symbol_make "LOCAL"
val () = symbol_set_fullname (LOCAL, "\"local\"")
val () = symbol_set_tyname (LOCAL, t0kn_tyname)
//
val MACDEF = symbol_make "MACDEF"
val () = symbol_set_fullname (MACDEF, "\"macdef\"")
val () = symbol_set_tyname (MACDEF, t0kn_tyname)
val MACRODEF = symbol_make "MACRODEF"
val () = symbol_set_fullname (MACRODEF, "\"macrodef\"")
val () = symbol_set_tyname (MACRODEF, t0kn_tyname)
//
val NONFIX = symbol_make "NONFIX"
val () = symbol_set_fullname (NONFIX, "\"nonfix\"")
val () = symbol_set_tyname (NONFIX, t0kn_tyname)
//
val OF = symbol_make "OF"
val () = symbol_set_fullname (OF, "\"of\"")
val () = symbol_set_tyname (OF, t0kn_tyname)
//
val OP = symbol_make "OP"
val () = symbol_set_fullname (OP, "\"op\"")
val () = symbol_set_tyname (OP, t0kn_tyname)
//
val OVERLOAD = symbol_make "OVERLOAD"
val () = symbol_set_fullname (OVERLOAD, "\"overload\"")
val () = symbol_set_tyname (OVERLOAD, t0kn_tyname)
//
val PAR = symbol_make "PAR"
val () = symbol_set_fullname (PAR, "\"par\"")
val () = symbol_set_tyname (PAR, t0kn_tyname)
//
val POSTFIX = symbol_make "POSTFIX"
val () = symbol_set_fullname (POSTFIX, "\"postfix\"")
val () = symbol_set_tyname (POSTFIX, t0kn_tyname)
//
val PRAXI = symbol_make "PRAXI"
val () = symbol_set_fullname (PRAXI, "\"praxi\"")
val () = symbol_set_tyname (PRAXI, t0kn_tyname)
//
val PRFN = symbol_make "PRFN"
val () = symbol_set_fullname (PRFN, "\"prfn\"")
val () = symbol_set_tyname (PRFN, t0kn_tyname)
//
val PRFUN = symbol_make "PRFUN"
val () = symbol_set_fullname (PRFUN, "\"prfun\"")
val () = symbol_set_tyname (PRFUN, t0kn_tyname)
//
val PROPDEF = symbol_make "PROPDEF"
val () = symbol_set_fullname (PROPDEF, "\"propdef\"")
val () = symbol_set_tyname (PROPDEF, t0kn_tyname)
val PROPMINUS = symbol_make "PROPMINUS"
val () = symbol_set_fullname (PROPMINUS, "\"prop-\"")
val () = symbol_set_tyname (PROPMINUS, t0kn_tyname)
val PROPPLUS = symbol_make "PROPPLUS"
val () = symbol_set_fullname (PROPPLUS, "\"prop+\"")
val () = symbol_set_tyname (PROPPLUS, t0kn_tyname)
//
val PRVAL = symbol_make "PRVAL"
val () = symbol_set_fullname (PRVAL, "\"prval\"")
val () = symbol_set_tyname (PRVAL, t0kn_tyname)
//
val REC = symbol_make "REC"
val () = symbol_set_fullname (REC, "\"rec\"")
val () = symbol_set_tyname (REC, t0kn_tyname)
//
val R0EAD = symbol_make "R0EAD"
val () = symbol_set_fullname (R0EAD, "\"r0ead\"")
val () = symbol_set_tyname (R0EAD, t0kn_tyname)
//
val SCASE = symbol_make "SCASE"
val () = symbol_set_fullname (SCASE, "\"scase\"")
val () = symbol_set_tyname (SCASE, t0kn_tyname)
//
val SIF = symbol_make "SIF"
val () = symbol_set_fullname (SIF, "\"sif\"")
val () = symbol_set_tyname (SIF, t0kn_tyname)
//
val SORTDEF = symbol_make "SORTDEF"
val () = symbol_set_fullname (SORTDEF, "\"sortdef\"")
val () = symbol_set_tyname (SORTDEF, t0kn_tyname)
//
val STA = symbol_make "STA"
val () = symbol_set_fullname (STA, "\"sta\"")
val () = symbol_set_tyname (STA, t0kn_tyname)
//
val STADEF = symbol_make "STADEF"
val () = symbol_set_fullname (STADEF, "\"stadef\"")
val () = symbol_set_tyname (STADEF, t0kn_tyname)
//
val STAIF = symbol_make "STAIF"
val () = symbol_set_fullname (STAIF, "\"staif\"")
val () = symbol_set_tyname (STAIF, t0kn_tyname)
//
val STALOAD = symbol_make "STALOAD"
val () = symbol_set_fullname (STALOAD, "\"staload\"")
val () = symbol_set_tyname (STALOAD, t0kn_tyname)
//
val STAVAR = symbol_make "STAVAR"
val () = symbol_set_fullname (STAVAR, "\"stavar\"")
val () = symbol_set_tyname (STAVAR, t0kn_tyname)
//
val SYMELIM = symbol_make "SYMELIM"
val () = symbol_set_fullname (SYMELIM, "\"symelim\"")
val () = symbol_set_tyname (SYMELIM, t0kn_tyname)
val SYMINTR = symbol_make "SYMINTR"
val () = symbol_set_fullname (SYMINTR, "\"symintr\"")
val () = symbol_set_tyname (SYMINTR, t0kn_tyname)
//
val THEN = symbol_make "THEN"
val () = symbol_set_fullname (THEN, "\"then\"")
val () = symbol_set_tyname (THEN, t0kn_tyname)
//
val TRY = symbol_make "TRY"
val () = symbol_set_fullname (TRY, "\"try\"")
val () = symbol_set_tyname (TRY, t0kn_tyname)
//
val TYPEDEF = symbol_make "TYPEDEF"
val () = symbol_set_fullname (TYPEDEF, "\"typedef\"")
val () = symbol_set_tyname (TYPEDEF, t0kn_tyname)
val TYPEMINUS = symbol_make "TYPEMINUS"
val () = symbol_set_fullname (TYPEMINUS, "\"type-\"")
val () = symbol_set_tyname (TYPEMINUS, t0kn_tyname)
val TYPEPLUS = symbol_make "TYPEPLUS"
val () = symbol_set_fullname (TYPEPLUS, "\"type+\"")
val () = symbol_set_tyname (TYPEPLUS, t0kn_tyname)
//
val T0YPE = symbol_make "T0YPE"
val () = symbol_set_fullname (T0YPE, "\"t@ype\"")
val () = symbol_set_tyname (T0YPE, t0kn_tyname)
val T0YPEMINUS = symbol_make "T0YPEMINUS"
val () = symbol_set_fullname (T0YPEMINUS, "\"t@ype-\"")
val () = symbol_set_tyname (T0YPEMINUS, t0kn_tyname)
val T0YPEPLUS = symbol_make "T0YPEPLUS"
val () = symbol_set_fullname (T0YPEPLUS, "\"t@ype+\"")
val () = symbol_set_tyname (T0YPEPLUS, t0kn_tyname)
//
val VAL = symbol_make "VAL"
val () = symbol_set_fullname (VAL, "\"val\"")
val () = symbol_set_tyname (VAL, t0kn_tyname)
val VALMINUS = symbol_make "VALMINUS"
val () = symbol_set_fullname (VALMINUS, "\"val-\"")
val () = symbol_set_tyname (VALMINUS, t0kn_tyname)
val VALPLUS = symbol_make "VALPLUS"
val () = symbol_set_fullname (VALPLUS, "\"val+\"")
val () = symbol_set_tyname (VALPLUS, t0kn_tyname)
//
val VAR = symbol_make "VAR"
val () = symbol_set_fullname (VAR, "\"var\"")
val () = symbol_set_tyname (VAR, t0kn_tyname)
//
val VIEWDEF = symbol_make "VIEWDEF"
val () = symbol_set_fullname (VIEWDEF, "\"viewdef\"")
val () = symbol_set_tyname (VIEWDEF, t0kn_tyname)
val VIEWMINUS = symbol_make "VIEWMINUS"
val () = symbol_set_fullname (VIEWMINUS, "\"view-\"")
val () = symbol_set_tyname (VIEWMINUS, t0kn_tyname)
val VIEWPLUS = symbol_make "VIEWPLUS"
val () = symbol_set_fullname (VIEWPLUS, "\"view+\"")
val () = symbol_set_tyname (VIEWPLUS, t0kn_tyname)
//
val VIEWTYPEDEF = symbol_make "VIEWTYPEDEF"
val () = symbol_set_fullname (VIEWTYPEDEF, "\"viewtypedef\"")
val () = symbol_set_tyname (VIEWTYPEDEF, t0kn_tyname)
val VIEWTYPEMINUS = symbol_make "VIEWTYPEMINUS"
val () = symbol_set_fullname (VIEWTYPEMINUS, "\"viewtype-\"")
val () = symbol_set_tyname (VIEWTYPEMINUS, t0kn_tyname)
val VIEWTYPEPLUS = symbol_make "VIEWTYPEPLUS"
val () = symbol_set_fullname (VIEWTYPEPLUS, "\"viewtype+\"")
val () = symbol_set_tyname (VIEWTYPEPLUS, t0kn_tyname)
//
val VIEWT0YPE = symbol_make "VIEWT0YPE"
val () = symbol_set_fullname (VIEWT0YPE, "\"viewt@ype\"")
val () = symbol_set_tyname (VIEWT0YPE, t0kn_tyname)
val VIEWT0YPEMINUS = symbol_make "VIEWT0YPEMINUS"
val () = symbol_set_fullname (VIEWT0YPEMINUS, "\"viewt@ype-\"")
val () = symbol_set_tyname (VIEWT0YPEMINUS, t0kn_tyname)
val VIEWT0YPEPLUS = symbol_make "VIEWT0YPEPLUS"
val () = symbol_set_fullname (VIEWT0YPEPLUS, "\"viewt@ype+\"")
val () = symbol_set_tyname (VIEWT0YPEPLUS, t0kn_tyname)
//
val WHEN = symbol_make "WHEN"
val () = symbol_set_fullname (WHEN, "\"when\"")
val () = symbol_set_tyname (WHEN, t0kn_tyname)
//
val WHERE = symbol_make "WHERE"
val () = symbol_set_fullname (WHERE, "\"where\"")
val () = symbol_set_tyname (WHERE, t0kn_tyname)
//
val WHILE = symbol_make "WHILE"
val () = symbol_set_fullname (WHILE, "\"while\"")
val () = symbol_set_tyname (WHILE, t0kn_tyname)
val WHILESTAR = symbol_make "WHILESTAR"
val () = symbol_set_fullname (WHILESTAR, "\"while*\"")
val () = symbol_set_tyname (WHILESTAR, t0kn_tyname)
//
val WITH = symbol_make "WITH"
val () = symbol_set_fullname (WITH, "\"with\"")
val () = symbol_set_tyname (WITH, t0kn_tyname)
//
val WITHPROP = symbol_make "WITHPROP"
val () = symbol_set_fullname (WITHPROP, "\"withprop\"")
val () = symbol_set_tyname (WITHPROP, t0kn_tyname)
val WITHTYPE = symbol_make "WITHTYPE"
val () = symbol_set_fullname (WITHTYPE, "\"withtype\"")
val () = symbol_set_tyname (WITHTYPE, t0kn_tyname)
val WITHVIEW = symbol_make "WITHVIEW"
val () = symbol_set_fullname (WITHVIEW, "\"withview\"")
val () = symbol_set_tyname (WITHVIEW, t0kn_tyname)
val WITHVIEWTYPE = symbol_make "WITHVIEWTYPE"
val () = symbol_set_fullname (WITHVIEWTYPE, "\"withviewtype\"")
val () = symbol_set_tyname (WITHVIEWTYPE, t0kn_tyname)
//
(* ****** ****** *)
//
val AMPERSAND = symbol_make ("AMPERSAND")
val () = symbol_set_fullname (AMPERSAND, "\"&\"")
val () = symbol_set_tyname (AMPERSAND, t0kn_tyname)
//
val BACKQUOTE = symbol_make ("BACKQUOTE")
val () = symbol_set_fullname (BACKQUOTE, "\"`\"")
val () = symbol_set_tyname (BACKQUOTE, t0kn_tyname)
//
val BACKSLASH = symbol_make ("BACKSLASH")
val () = symbol_set_fullname (BACKSLASH, "\"\\\"")
val () = symbol_set_tyname (BACKSLASH, t0kn_tyname)
//
val BANG = symbol_make ("BANG")
val () = symbol_set_fullname (BANG, "\"!\"")
val () = symbol_set_tyname (BANG, t0kn_tyname)
//
val BAR = symbol_make ("BAR")
val () = symbol_set_fullname (BAR, "\"|\"")
val () = symbol_set_tyname (BAR, t0kn_tyname)
//
val COMMA = symbol_make ("COMMA")
val () = symbol_set_fullname (COMMA, "\",\"")
val () = symbol_set_tyname (COMMA, t0kn_tyname)
//
val COLON = symbol_make ("COLON")
val () = symbol_set_fullname (COLON, "\":\"")
val () = symbol_set_tyname (COLON, t0kn_tyname)
//
val SEMICOLON = symbol_make ("SEMICOLON")
val () = symbol_set_fullname (SEMICOLON, "\";\"")
val () = symbol_set_tyname (SEMICOLON, t0kn_tyname)
//
val DOT = symbol_make ("DOT")
val () = symbol_set_fullname (DOT, "\".\"")
val () = symbol_set_tyname (DOT, t0kn_tyname)
//
val EQ = symbol_make ("EQ")
val () = symbol_set_fullname (EQ, "\"=\"")
val () = symbol_set_tyname (EQ, t0kn_tyname)
//
val LT = symbol_make ("LT")
val () = symbol_set_fullname (LT, "\"<\"")
val () = symbol_set_tyname (LT, t0kn_tyname)
val GT = symbol_make ("GT")
val () = symbol_set_fullname (GT, "\">\"")
val () = symbol_set_tyname (GT, t0kn_tyname)
//
val DOLLAR = symbol_make ("DOLLAR")
val () = symbol_set_fullname (DOLLAR, "\"$\"")
val () = symbol_set_tyname (DOLLAR, t0kn_tyname)
//
val HASH = symbol_make ("HASH")
val () = symbol_set_fullname (HASH, "\"#\"")
val () = symbol_set_tyname (HASH, t0kn_tyname)
//
val TILDA = symbol_make ("TILDA")
val () = symbol_set_fullname (TILDA, "\"~\"")
val () = symbol_set_tyname (TILDA, t0kn_tyname)
//
val DOTDOT = symbol_make ("DOTDOT")
val () = symbol_set_fullname (DOTDOT, "\"..\"")
val () = symbol_set_tyname (DOTDOT, t0kn_tyname)
val DOTDOTDOT = symbol_make ("DOTDOTDOT")
val () = symbol_set_fullname (DOTDOTDOT, "\"...\"")
val () = symbol_set_tyname (DOTDOTDOT, t0kn_tyname)
//
val EQLT = symbol_make ("EQLT")
val () = symbol_set_fullname (EQLT, "\"=<\"")
val () = symbol_set_tyname (EQLT, t0kn_tyname)
val EQGT = symbol_make ("EQGT")
val () = symbol_set_fullname (EQGT, "\"=>\"")
val () = symbol_set_tyname (EQGT, t0kn_tyname)
val EQLTGT = symbol_make ("EQLTGT")
val () = symbol_set_fullname (EQLTGT, "\"=<>\"")
val () = symbol_set_tyname (EQLTGT, t0kn_tyname)
val EQGTGT = symbol_make ("EQGTGT")
val () = symbol_set_fullname (EQGTGT, "\"=>>\"")
val () = symbol_set_tyname (EQGTGT, t0kn_tyname)
//
val EQSLASHEQGT = symbol_make ("EQSLASHEQGT")
val () = symbol_set_fullname (EQSLASHEQGT, "\"=/=>\"")
val () = symbol_set_tyname (EQSLASHEQGT, t0kn_tyname)
val EQSLASHEQGTGT = symbol_make ("EQSLASHEQGTGT")
val () = symbol_set_fullname (EQSLASHEQGTGT, "\"=/=>>\"")
val () = symbol_set_tyname (EQSLASHEQGTGT, t0kn_tyname)
//
val GTLT = symbol_make ("GTLT")
val () = symbol_set_fullname (GTLT, "\"<>\"")
val () = symbol_set_tyname (GTLT, t0kn_tyname)
//
val DOTLT = symbol_make ("DOTLT")
val () = symbol_set_fullname (DOTLT, "\".<\"")
val () = symbol_set_tyname (DOTLT, t0kn_tyname)
val GTDOT = symbol_make ("GTDOT")
val () = symbol_set_fullname (GTDOT, "\">.\"")
val () = symbol_set_tyname (GTDOT, t0kn_tyname)
val DOTLTGTDOT = symbol_make ("DOTLTGTDOT")
val () = symbol_set_fullname (DOTLTGTDOT, "\".<>.\"")
val () = symbol_set_tyname (DOTLTGTDOT, t0kn_tyname)
//
val MINUSLT = symbol_make ("MINUSLT")
val () = symbol_set_fullname (MINUSLT, "\"-<\"")
val () = symbol_set_tyname (MINUSLT, t0kn_tyname)
val MINUSGT = symbol_make ("MINUSGT")
val () = symbol_set_fullname (MINUSGT, "\"->\"")
val () = symbol_set_tyname (MINUSGT, t0kn_tyname)
val MINUSLTGT = symbol_make ("MINUSLTGT")
val () = symbol_set_fullname (MINUSLTGT, "\"-<>\"")
val () = symbol_set_tyname (MINUSLTGT, t0kn_tyname)
//
val COLONLT = symbol_make ("COLONLT")
val () = symbol_set_fullname (COLONLT, "\":<\"")
val () = symbol_set_tyname (COLONLT, t0kn_tyname)
val COLONLTGT = symbol_make ("COLONLTGT")
val () = symbol_set_fullname (COLONLTGT, "\":<>\"")
val () = symbol_set_tyname (COLONLTGT, t0kn_tyname)
//
val BACKQUOTELPAREN = symbol_make ("BACKQUOTELPAREN")
val () = symbol_set_fullname (BACKQUOTELPAREN, "\"`(\"")
val () = symbol_set_tyname (BACKQUOTELPAREN, t0kn_tyname)
val COMMALPAREN = symbol_make ("COMMALPAREN")
val () = symbol_set_fullname (COMMALPAREN, "\",(\"")
val () = symbol_set_tyname (COMMALPAREN, t0kn_tyname)
val PERCENTLPAREN = symbol_make ("PERCENTLPAREN")
val () = symbol_set_fullname (PERCENTLPAREN, "\"%(\"")
val () = symbol_set_tyname (PERCENTLPAREN, t0kn_tyname)
(*
//
// HX: these symbols were reserved for supporting MP
//
val BACKQUOTELBRACKET = symbol_make ("BACKQUOTELBRACKET")
val () = symbol_set_fullname (BACKQUOTELBRACKET, "\"`[\"")
val () = symbol_set_tyname (BACKQUOTELBRACKET, t0kn_tyname)
val PERCENTLBRACKET = symbol_make ("PERCENTLBRACKET")
val () = symbol_set_fullname (COMMALBRACE, "\"%[\"")
val () = symbol_set_tyname (PERCENTLBRACKET, t0kn_tyname)
val COMMALBRACKET = symbol_make ("COMMALBRACKET")
val () = symbol_set_fullname (COMMALBRACKET, "\",[\"")
val () = symbol_set_tyname (COMMALBRACKET, t0kn_tyname)
//
val BACKQUOTELBRACE = symbol_make ("BACKQUOTELBRACE")
val () = symbol_set_fullname (BACKQUOTELBRACE, "\"`{\"")
val () = symbol_set_tyname (BACKQUOTELBRACE, t0kn_tyname)
val PERCENTLBRACE = symbol_make ("PERCENTLBRACE")
val () = symbol_set_fullname (COMMALBRACE, "\"%{\"")
val () = symbol_set_tyname (PERCENTLBRACE, t0kn_tyname)
val COMMALBRACE = symbol_make ("COMMALBRACE")
val () = symbol_set_fullname (COMMALBRACE, "\",{\"")
val () = symbol_set_tyname (COMMALBRACE, t0kn_tyname)
*)
(* ****** ****** *)
//
val DLRARRSZ = symbol_make "DLRARRSZ"
val () = symbol_set_fullname (DLRARRSZ, "\"$arrsz\"")
val () = symbol_set_tyname (DLRARRSZ, t0kn_tyname)
//
val DLRLST_T = symbol_make "DLRLST_T"
val () = symbol_set_fullname (DLRLST_T, "\"$lst_t\"")
val () = symbol_set_tyname (DLRLST_T, t0kn_tyname)
val DLRLST_VT = symbol_make "DLRLST_VT"
val () = symbol_set_fullname (DLRLST_VT, "\"$lst_vt\"")
val () = symbol_set_tyname (DLRLST_VT, t0kn_tyname)
//
val DLRREC_T = symbol_make "DLRREC_T"
val () = symbol_set_fullname (DLRREC_T, "\"$rec_t\"")
val () = symbol_set_tyname (DLRREC_T, t0kn_tyname)
val DLRREC_VT = symbol_make "DLRREC_VT"
val () = symbol_set_fullname (DLRREC_VT, "\"$rec_vt\"")
val () = symbol_set_tyname (DLRREC_VT, t0kn_tyname)
//
val DLRTUP_T = symbol_make "DLRTUP_T"
val () = symbol_set_fullname (DLRTUP_T, "\"$tup_t\"")
val () = symbol_set_tyname (DLRTUP_T, t0kn_tyname)
val DLRTUP_VT = symbol_make "DLRTUP_VT"
val () = symbol_set_fullname (DLRTUP_VT, "\"$tup_vt\"")
val () = symbol_set_tyname (DLRTUP_VT, t0kn_tyname)
//
val DLRDELAY = symbol_make "DLRDELAY"
val () = symbol_set_fullname (DLRDELAY, "\"$delay\"")
val () = symbol_set_tyname (DLRDELAY, t0kn_tyname)
val DLRLDELAY = symbol_make "DLRLDELAY"
val () = symbol_set_fullname (DLRLDELAY, "\"$ldelay\"")
val () = symbol_set_tyname (DLRLDELAY, t0kn_tyname)
//
val DLRDYNLOAD = symbol_make "DLRDYNLOAD"
val () = symbol_set_fullname (DLRDYNLOAD, "\"$dynload\"")
val () = symbol_set_tyname (DLRDYNLOAD, t0kn_tyname)
//
val DLREFFMASK_ALL = symbol_make "DLREFFMASK_ALL"
val () = symbol_set_fullname (DLREFFMASK_ALL, "\"$effmask_all\"")
val () = symbol_set_tyname (DLREFFMASK_ALL, t0kn_tyname)
//
val DLREFFMASK_EXN = symbol_make "DLREFFMASK_EXN"
val () = symbol_set_fullname (DLREFFMASK_EXN, "\"$effmask_exn\"")
val () = symbol_set_tyname (DLREFFMASK_EXN, t0kn_tyname)
//
val DLREFFMASK_NTM = symbol_make "DLREFFMASK_NTM"
val () = symbol_set_fullname (DLREFFMASK_NTM, "\"$effmask_ntm\"")
val () = symbol_set_tyname (DLREFFMASK_NTM, t0kn_tyname)
//
val DLREFFMASK_REF = symbol_make "DLREFFMASK_REF"
val () = symbol_set_fullname (DLREFFMASK_REF, "\"$effmask_ref\"")
val () = symbol_set_tyname (DLREFFMASK_REF, t0kn_tyname)
//
val DLRDECRYPT = symbol_make "DLRDECRYPT"
val () = symbol_set_fullname (DLRDECRYPT, "\"$decrypt\"")
val () = symbol_set_tyname (DLRDECRYPT, t0kn_tyname)
val DLRENCRYPT = symbol_make "DLRENCRYPT"
val () = symbol_set_fullname (DLRENCRYPT, "\"$encrypt\"")
val () = symbol_set_tyname (DLRENCRYPT, t0kn_tyname)
//
val DLREXTERN = symbol_make "DLREXTERN"
val () = symbol_set_fullname (DLREXTERN, "\"$extern\"")
val () = symbol_set_tyname (DLREXTERN, t0kn_tyname)
val DLREXTVAL = symbol_make "DLREXTVAL"
val () = symbol_set_fullname (DLREXTVAL, "\"$extval\"")
val () = symbol_set_tyname (DLREXTVAL, t0kn_tyname)
//
val DLREXTYPE = symbol_make "DLREXTYPE"
val () = symbol_set_fullname (DLREXTYPE, "\"$extype\"")
val () = symbol_set_tyname (DLREXTYPE, t0kn_tyname)
val DLREXTYPE_STRUCT = symbol_make "DLREXTYPE_STRUCT"
val () = symbol_set_fullname (DLREXTYPE_STRUCT, "\"$extype_struct\"")
val () = symbol_set_tyname (DLREXTYPE_STRUCT, t0kn_tyname)
//
val DLRFOLD = symbol_make "DLRFOLD"
val () = symbol_set_fullname (DLRFOLD, "\"$fold\"")
val () = symbol_set_tyname (DLRFOLD, t0kn_tyname)
val DLRUNFOLD = symbol_make "DLRUNFOLD"
val () = symbol_set_fullname (DLRUNFOLD, "\"$unfold\"")
val () = symbol_set_tyname (DLRUNFOLD, t0kn_tyname)
//
val DLRRAISE = symbol_make "DLRRAISE"
val () = symbol_set_fullname (DLRRAISE, "\"$raise\"")
val () = symbol_set_tyname (DLRRAISE, t0kn_tyname)
//
val DLRTYPEOF = symbol_make "DLRTYPEOF"
val () = symbol_set_fullname (DLRTYPEOF, "\"$typeof\"")
val () = symbol_set_tyname (DLRTYPEOF, t0kn_tyname)
//
(* ****** ****** *)
//
val SRPFILENAME = symbol_make "SRPFILENAME"
val () = symbol_set_fullname (SRPFILENAME, "\"#FILENAME\"")
val () = symbol_set_tyname (SRPFILENAME, t0kn_tyname)
val SRPLOCATION = symbol_make "SRPLOCATION"
val () = symbol_set_fullname (SRPLOCATION, "\"#LOCATION\"")
val () = symbol_set_tyname (SRPLOCATION, t0kn_tyname)
val SRPCHARCOUNT = symbol_make "SRPCHARCOUNT"
val () = symbol_set_fullname (SRPCHARCOUNT, "\"#CHARCOUNT\"")
val () = symbol_set_tyname (SRPCHARCOUNT, t0kn_tyname)
val SRPLINECOUNT = symbol_make "SRPLINECOUNT"
val () = symbol_set_fullname (SRPLINECOUNT, "\"#LINECOUNT\"")
val () = symbol_set_tyname (SRPLINECOUNT, t0kn_tyname)
//
val SRPASSERT = symbol_make "SRPASSERT"
val () = symbol_set_fullname (SRPASSERT, "\"#assert\"")
val () = symbol_set_tyname (SRPASSERT, t0kn_tyname)
val SRPDEFINE = symbol_make "SRPDEFINE"
val () = symbol_set_fullname (SRPDEFINE, "\"#define\"")
val () = symbol_set_tyname (SRPDEFINE, t0kn_tyname)
val SRPELSE = symbol_make "SRPELSE"
val () = symbol_set_fullname (SRPELSE, "\"#else\"")
val () = symbol_set_tyname (SRPELSE, t0kn_tyname)
val SRPELIF = symbol_make "SRPELIF"
val () = symbol_set_fullname (SRPELIF, "\"#elif\"")
val () = symbol_set_tyname (SRPELIF, t0kn_tyname)
val SRPELIFDEF = symbol_make "SRPELIFDEF"
val () = symbol_set_fullname (SRPELIFDEF, "\"#elifdef\"")
val () = symbol_set_tyname (SRPELIFDEF, t0kn_tyname)
val SRPELIFNDEF = symbol_make "SRPELIFNDEF"
val () = symbol_set_fullname (SRPELIFNDEF, "\"#elifndef\"")
val () = symbol_set_tyname (SRPELIFNDEF, t0kn_tyname)
val SRPENDIF = symbol_make "SRPENDIF"
val () = symbol_set_fullname (SRPENDIF, "\"#endif\"")
val () = symbol_set_tyname (SRPENDIF, t0kn_tyname)
val SRPERROR = symbol_make "SRPERROR"
val () = symbol_set_fullname (SRPERROR, "\"#error\"")
val () = symbol_set_tyname (SRPERROR, t0kn_tyname)
val SRPIF = symbol_make "SRPIF"
val () = symbol_set_fullname (SRPIF, "\"#if\"")
val () = symbol_set_tyname (SRPIF, t0kn_tyname)
val SRPIFDEF = symbol_make "SRPIFDEF"
val () = symbol_set_fullname (SRPIFDEF, "\"#ifdef\"")
val () = symbol_set_tyname (SRPIFDEF, t0kn_tyname)
val SRPIFNDEF = symbol_make "SRPIFNDEF"
val () = symbol_set_fullname (SRPIFNDEF, "\"#ifndef\"")
val () = symbol_set_tyname (SRPIFNDEF, t0kn_tyname)
val SRPINCLUDE = symbol_make "SRPINCLUDE"
val () = symbol_set_fullname (SRPINCLUDE, "\"#include\"")
val () = symbol_set_tyname (SRPINCLUDE, t0kn_tyname)
val SRPPRINT = symbol_make "SRPPRINT"
val () = symbol_set_fullname (SRPPRINT, "\"#print\"")
val () = symbol_set_tyname (SRPPRINT, t0kn_tyname)
val SRPTHEN = symbol_make "SRPTHEN"
val () = symbol_set_fullname (SRPTHEN, "\"#then\"")
val () = symbol_set_tyname (SRPTHEN, t0kn_tyname)
val SRPUNDEF = symbol_make "SRPUNDEF"
val () = symbol_set_fullname (SRPUNDEF, "\"#undef\"")
val () = symbol_set_tyname (SRPUNDEF, t0kn_tyname)
//
(* ****** ****** *)
//
val FOLDAT = symbol_make "FOLDAT"
val () = symbol_set_fullname (FOLDAT, "\"fold@\"")
val () = symbol_set_tyname (FOLDAT, t0kn_tyname)
//
val FREEAT = symbol_make "FREEAT"
val () = symbol_set_fullname (FREEAT, "\"free@\"")
val () = symbol_set_tyname (FREEAT, t0kn_tyname)
//
val VIEWAT = symbol_make "VIEWAT"
val () = symbol_set_fullname (VIEWAT, "\"view@\"")
val () = symbol_set_tyname (VIEWAT, t0kn_tyname)
//
(* ****** ****** *)

val theStartEntry = symbol_make_nt "theStartEntry"
val () = symbol_set_fullname (theStartEntry, "program")

(* ****** ****** *)
//
val abskind = symbol_make_nt "abskind"
val dcstkind = symbol_make_nt "dcstkind"
val datakind = symbol_make_nt "datakind"
val stadefkind = symbol_make_nt "stadefkind"
//
val valkind = symbol_make_nt "valkind"
val funkind = symbol_make_nt "funkind"
//
val lamkind = symbol_make_nt "lamkind"
val fixkind = symbol_make_nt "fixkind"
//
val srpifkind = symbol_make_nt "srpifkind"
val srpelifkind = symbol_make_nt "srpelifkind"
val srpthenopt = symbol_make_nt "srpthenopt"
//
(* ****** ****** *)

val i0de = symbol_make_nt "i0de"
val i0de_dlr = symbol_make_nt "i0de_dlr"
val i0deseq = symbol_make_nt "i0deseq"
val i0dext = symbol_make_nt "i0dext"

(* ****** ****** *)

val e0xp = symbol_make_nt "e0xp"

(* ****** ****** *)

val s0rt = symbol_make_nt "s0rt"
val s0rtq = symbol_make_nt "s0rtq"
val s0rtid = symbol_make_nt "s0rtid"
val atms0rt = symbol_make_nt "atms0rt"
val s0rtseq = symbol_make_nt "s0rtseq"
val commas0rtseq = symbol_make_nt "commas0rtseq"
val s0rtpol = symbol_make_nt "s0rtpol"

(* ****** ****** *)
//
val d0ec = symbol_make_nt "d0ec"
//
val d0ecarg = symbol_make_nt "d0ecarg"
val d0ecargseq = symbol_make_nt "d0ecargseq"
//
val semicolonseq = symbol_make_nt "semicolonseq"
//
val d0ec_sta = symbol_make_nt "d0ec_sta"
val guad0ec_sta = symbol_make_nt "guad0ec_sta"
val d0ecseq_sta = symbol_make_nt "d0ecseq_sta"
val d0ecseq_sta_rev = symbol_make_nt "d0ec_staseq_rev"
//
val d0ec_dyn = symbol_make_nt "d0ec_dyn"
val guad0ec_dyn = symbol_make_nt "guad0ec_dyn"
val d0ecseq_dyn = symbol_make_nt "d0ecseq_dyn"
val d0ecseq_dyn_rev = symbol_make_nt "d0ecseq_dyn_rev"

(* ****** ****** *)

(*
theStartEntry
  : ISSTATIC d0ecseq_sta TOKEN_eof      { $$ = $2 ; return 0 ; }
  | ISDYNAMIC d0ecseq_dyn TOKEN_eof     { $$ = $2 ; return 0 ; }
; /* end of [theStartEntry] */
*)
fun theStartEntry_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (theStartEntry)
//
val gr = grmrule_append
  ($lst_t {symbol} (tupz! ISSTATIC d0ecseq_sta TOKEN_eof))
val () = grmrule_set_action (gr, "{ $$ = $2 ; return 0 ; }")
//
val gr = grmrule_append
  ($lst_t {symbol} (tupz! ISDYNAMIC d0ecseq_dyn TOKEN_eof))
val () = grmrule_set_action (gr, "{ $$ = $2 ; return 0 ; }")
//
val () = symbol_close (pf | theStartEntry)
} // end of [theStartEntry_proc]

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
val gr = grmrule_append (ABSPROP)
val () = grmrule_set_action (gr, "{ $$ = abskind_prop () ; }")
val gr = grmrule_append (ABSTYPE)
val () = grmrule_set_action (gr, "{ $$ = abskind_type () ; }")
val gr = grmrule_append (ABST0YPE)
val () = grmrule_set_action (gr, "{ $$ = abskind_t0ype () ; }")
val gr = grmrule_append (ABSVIEW)
val () = grmrule_set_action (gr, "{ $$ = abskind_view () ; }")
val gr = grmrule_append (ABSVIEWTYPE)
val () = grmrule_set_action (gr, "{ $$ = abskind_viewtype () ; }")
val gr = grmrule_append (ABSVIEWT0YPE)
val () = grmrule_set_action (gr, "{ $$ = abskind_viewt0ype () ; }")
//
val () = symbol_close (pf | abskind)
} // end of [abskind_proc]

(* ****** ****** *)

(*
dcstkind
  : FUN                                 { $$ = dcstkind_fun () ; }
  | VAL                                 { $$ = dcstkind_val () ; }
  | CASTFN                              { $$ = dcstkind_castfn () ; }
  | PRAXI                               { $$ = dcstkind_praxi () ; }
  | PRFUN                               { $$ = dcstkind_prfun () ; }
  | PRVAL                               { $$ = dcstkind_prval () ; }
;
*)
fun dcstkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (dcstkind)
//
val gr = grmrule_append (FUN)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_fun () ; }")
val gr = grmrule_append (VAL)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_val () ; }")
val gr = grmrule_append (CASTFN)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_castfn () ; }")
val gr = grmrule_append (PRAXI)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_praxi () ; }")
val gr = grmrule_append (PRFUN)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_prfun () ; }")
val gr = grmrule_append (PRVAL)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_prval () ; }")
//
val () = symbol_close (pf | dcstkind)
} // end of [dcstkind_proc]

(* ****** ****** *)

(*
datakind
  : DATAPROP                            { $$ = datakind_prop () ; }
  | DATATYPE                            { $$ = datakind_type () ; }
  | DATAVIEW                            { $$ = datakind_view () ; }
  | DATAVIEWTYPE                        { $$ = datakind_viewtype () ; }
;
*)
fun datakind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (datakind)
//
val gr = grmrule_append (DATAPROP)
val () = grmrule_set_action (gr, "{ $$ = datakind_prop () ; }")
val gr = grmrule_append (DATATYPE)
val () = grmrule_set_action (gr, "{ $$ = datakind_type () ; }")
val gr = grmrule_append (DATAVIEW)
val () = grmrule_set_action (gr, "{ $$ = datakind_view () ; }")
val gr = grmrule_append (DATAVIEWTYPE)
val () = grmrule_set_action (gr, "{ $$ = datakind_viewtype () ; }")
//
val () = symbol_close (pf | datakind)
} // end of [datakind_proc]

(* ****** ****** *)

(*
stadefkind
  : STADEF                              { $$ = stadefkind_generic () ; }
  | PROPDEF                             { $$ = stadefkind_prop ($1) ; }
  | TYPEDEF                             { $$ = stadefkind_type ($1) ; }
  | VIEWDEF                             { $$ = stadefkind_view ($1) ; }
  | VIEWTYPEDEF                         { $$ = stadefkind_viewtype ($1) ; }
;
*)
fun stadefkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (stadefkind)
//
val gr = grmrule_append (STADEF)
val () = grmrule_set_action (gr, "{ $$ = stadefkind_generic () ; }")
val gr = grmrule_append (PROPDEF)
val () = grmrule_set_action (gr, "{ $$ = stadefkind_prop () ; }")
val gr = grmrule_append (TYPEDEF)
val () = grmrule_set_action (gr, "{ $$ = stadefkind_type () ; }")
val gr = grmrule_append (VIEWDEF)
val () = grmrule_set_action (gr, "{ $$ = stadefkind_view () ; }")
val gr = grmrule_append (VIEWTYPEDEF)
val () = grmrule_set_action (gr, "{ $$ = stadefkind_viewtype () ; }")
//
val () = symbol_close (pf | stadefkind)
} // end of [stadefkind_proc]

(* ****** ****** *)

(*
valkind
  : VAL                                 { $$ = valkind_val () ; }
  | VALMINUS                            { $$ = valkind_valminus () ; }
  | VALPLUS                             { $$ = valkind_valplus () ; }
  | PRVAL                               { $$ = valkind_prval () ; }
;
*)
fun valkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (valkind)
//
val gr = grmrule_append (VAL)
val () = grmrule_set_action (gr, "{ $$ = valkind_val () ; }")
val gr = grmrule_append (VALMINUS)
val () = grmrule_set_action (gr, "{ $$ = valkind_valminus () ; }")
val gr = grmrule_append (VALPLUS)
val () = grmrule_set_action (gr, "{ $$ = valkind_valplus () ; }")
val gr = grmrule_append (PRVAL)
val () = grmrule_set_action (gr, "{ $$ = valkind_prval () ; }")
//
val () = symbol_close (pf | valkind)
} // end of [valkind_proc]

(* ****** ****** *)

(*
funkind
  : FN                                  { $$ = funkind_fn () ; }
  | FNSTAR                              { $$ = funkind_fnstar () ; }
  | FUN                                 { $$ = funkind_fun () ; }
  | CASTFN                              { $$ = funkind_castfn () ; }
  | PRFN                                { $$ = funkind_prfn () ; }
  | PRFUN                               { $$ = funkind_prfun () ; }
;
*)
fun funkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (funkind)
//
val gr = grmrule_append (FN)
val () = grmrule_set_action (gr, "{ $$ = funkind_fn () ; }")
val gr = grmrule_append (FNSTAR)
val () = grmrule_set_action (gr, "{ $$ = funkind_fnstar () ; }")
val gr = grmrule_append (FUN)
val () = grmrule_set_action (gr, "{ $$ = funkind_fun () ; }")
val gr = grmrule_append (CASTFN)
val () = grmrule_set_action (gr, "{ $$ = funkind_castfn () ; }")
val gr = grmrule_append (PRFN)
val () = grmrule_set_action (gr, "{ $$ = funkind_prfn () ; }")
val gr = grmrule_append (PRFUN)
val () = grmrule_set_action (gr, "{ $$ = funkind_prfun () ; }")
//
val () = symbol_close (pf | funkind)
//
} // end of [funkind_proc]

(* ****** ****** *)

(*
lamkind
  : LAM                                 { $$ = lamkind_lam ($1) ; }
  | ATLAM                               { $$ = lamkind_atlam ($1) ; }
  | LLAM                                { $$ = lamkind_llam ($1) ; }
  | ATLLAM                              { $$ = lamkind_atllam ($1) ; }
;
*)
fun lamkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (lamkind)
//
val gr = grmrule_append (LAM)
val () = grmrule_set_action (gr, "{ $$ = lamkind_lam ($1) ; }")
val gr = grmrule_append (ATLAM)
val () = grmrule_set_action (gr, "{ $$ = lamkind_atlam ($1) ; }")
val gr = grmrule_append (LLAM)
val () = grmrule_set_action (gr, "{ $$ = lamkind_llam ($1) ; }")
val gr = grmrule_append (ATLLAM)
val () = grmrule_set_action (gr, "{ $$ = lamkind_atllam ($1) ; }")
//
val () = symbol_close (pf | lamkind)
//
} // end of [lamkind_proc]

(* ****** ****** *)

(*
fixkind
  : FIX                                 { $$ = fixkind_fix ($1) ; }
  | ATFIX                               { $$ = fixkind_atfix ($1) ; }
;
*)
fun fixkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (fixkind)
//
val gr = grmrule_append (FIX)
val () = grmrule_set_action (gr, "{ $$ = fixkind_fix ($1) ; }")
val gr = grmrule_append (ATFIX)
val () = grmrule_set_action (gr, "{ $$ = fixkind_atfix ($1) ; }")
//
val () = symbol_close (pf | fixkind)
//
} // end of [fixkind_proc]

(* ****** ****** *)

(*
srpifkind
  : SRPIF                               { $$ = srpifkindtok_if ($1) ; }
  | SRPIFDEF                            { $$ = srpifkindtok_ifdef ($1) ; }
  | SRPIFNDEF                           { $$ = srpifkindtok_ifndef ($1) ; }
;
*)
fun srpifkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (srpifkind)
//
val gr = grmrule_append (SRPIF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_if ($1) ; }")
val gr = grmrule_append (SRPIFDEF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_ifdef ($1) ; }")
val gr = grmrule_append (SRPIFNDEF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_ifndef ($1) ; }")
//
val () = symbol_close (pf | srpifkind)
//
} // end of [srpifkind]

(*
srpelifkind
  : SRPELIF                             { $$ = srpifkindtok_if ($1) ; }
  | SRPELIFDEF                          { $$ = srpifkindtok_ifdef ($1) ; }
  | SRPELIFNDEF                         { $$ = srpifkindtok_ifndef ($1) ; }
;
*)
fun srpelifkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (srpelifkind)
//
val gr = grmrule_append (SRPELIF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_if ($1) ; }")
val gr = grmrule_append (SRPELIFDEF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_ifdef ($1) ; }")
val gr = grmrule_append (SRPELIFNDEF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_ifndef ($1) ; }")
//
val () = symbol_close (pf | srpelifkind)
//
} // end of [srpelifkind]

(*
srpthenopt
  : /* empty */                         { ; }
  | SRPTHEN                             { ; }
;
*)
fun srpthenopt_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (srpthenopt)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ ; }")
val gr = grmrule_append (SRPTHEN)
val () = grmrule_set_action (gr, "{ ; }")
//
val () = theGrmrulelst_merge_all (srpthenopt, SYMREGopt(SRPTHEN))
//
val () = symbol_close (pf | srpthenopt)
//
} // end of [srpthenopt]

(* ****** ****** *)

(*
i0de /* identifier */
  : IDENTIFIER_alp                      { $$ = $1 ; }
  | IDENTIFIER_sym                      { $$ = $1 ; }
/* keysymb */
  | AMPERSAND                           { $$ = i0de_make_ampersand($1) ; }
  | BACKSLASH                           { $$ = i0de_make_backslash($1) ; }
  | BANG                                { $$ = i0de_make_bang($1) ; }
  | EQ                                  { $$ = i0de_make_eq($1) ; }
  | GT                                  { $$ = i0de_make_gt($1) ; }
  | LT                                  { $$ = i0de_make_lt($1) ; }
  | MINUSGT                             { $$ = i0de_make_minusgt($1) ; }
  | MINUSLTGT                           { $$ = i0de_make_minusltgt($1) ; }
  | TILDA                               { $$ = i0de_make_tilda($1) ; }
; /* end of [i0de] */
*)
fun i0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (i0de)
//
val gr = grmrule_append (IDENTIFIER_alp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append (IDENTIFIER_sym)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append (AMPERSAND)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_ampersand($1) ; }")
val gr = grmrule_append (BACKSLASH)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_backslash($1) ; }")
val gr = grmrule_append (BANG)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_bang($1) ; }")
val gr = grmrule_append (EQ)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_eq($1) ; }")
val gr = grmrule_append (GT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_gt($1) ; }")
val gr = grmrule_append (LT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_lt($1) ; }")
val gr = grmrule_append (MINUSGT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_minusgt($1) ; }")
val gr = grmrule_append (MINUSLTGT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_minusltgt($1) ; }")
val gr = grmrule_append (TILDA)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_tilda($1) ; }")
//
val () = symbol_close (pf | i0de)
//
} // end of [i0de_proc]

(* ****** ****** *)

(*
/* identifier beginning with $ */
  : IDENTIFIER_dlr                      { $$ = $1 ; }
; /* end of [i0de_dlr] */
*)
fun i0de_dlr_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (i0de_dlr)
//
val gr = grmrule_append (IDENTIFIER_dlr)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = symbol_close (pf | i0de_dlr)
//
} // end of [i0de_dlr_proc]

(* ****** ****** *)

(*
i0deseq /* identifier sequence */
  : /* empty */                         { $$ = i0delst_nil() ; }
  | i0de i0deseq                        { $$ = i0delst_cons($1, $2) ; }
; /* end of [i0deseq] */
*)
fun i0deseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (i0deseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = i0delst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de i0deseq))
val () = grmrule_set_action (gr, "{ $$ = i0delst_cons($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (i0deseq, SYMREGstar(i0de))
//
val () = symbol_close (pf | i0deseq)
//
} // end of [i0deseq_proc]

(* ****** ****** *)

(*
i0dext /* extern identifier for loading syndef */
  : IDENTIFIER_ext                      { $$ = $1 ; }
/* keyword */
  | DO                                  { $$ = i0de_make_DO($1) ; }
  | WHILE                               { $$ = i0de_make_WHILE($1) ; }
; /* end of [i0dext] */
*)
fun i0dext_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (i0dext)
//
val gr = grmrule_append (IDENTIFIER_ext)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append (DO)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_DO($1) ; }")
val gr = grmrule_append (WHILE)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_WHILE($1) ; }")
//
val () = symbol_close (pf | i0dext)
//
} // end of [i0dext_proc]

(* ****** ****** *)

(*
s0rtid /* sort identifier */
  : IDENTIFIER_alp                      { $$ = $1 ; }
  | IDENTIFIER_sym                      { $$ = $1 ; }
  | T0YPE                               { $$ = i0de_make_t0ype($1) ; }
  | VIEWT0YPE                           { $$ = i0de_make_viewt0ype($1) ; }
  | BACKSLASH                           { $$ = i0de_make_backslash($1) ; }
  | MINUSGT                             { $$ = i0de_make_minusgt($1) ; }
  | MINUSLTGT                           { $$ = i0de_make_minusltgt($1) ; }
; /* end of [s0rtid] */
*)
fun s0rtid_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0rtid)
//
val gr = grmrule_append (IDENTIFIER_alp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val gr = grmrule_append (IDENTIFIER_sym)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val gr = grmrule_append (T0YPE)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_t0ype($1) ; }")
//
val gr = grmrule_append (VIEWT0YPE)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_viewt0ype($1) ; }")
//
val gr = grmrule_append (BACKSLASH)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_backslash($1) ; }")
//
val gr = grmrule_append (MINUSGT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_minusgt($1) ; }")
//
val gr = grmrule_append (MINUSLTGT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_minusltgt($1) ; }")
//
val () = symbol_close (pf | s0rtid)
//
} // end of [s0rtid_proc]


(*
s0rtpol /* sort with polarity */
  : s0rt                                { $$ = s0rtpol_make($1, 0) ; }
  | PROPMINUS                           { $$ = s0rtpol_make(s0rt_prop($1), -1) ; }
  | PROPPLUS                            { $$ = s0rtpol_make(s0rt_prop($1),  1) ; }
  | TYPEMINUS                           { $$ = s0rtpol_make(s0rt_type($1), -1) ; }
  | TYPEPLUS                            { $$ = s0rtpol_make(s0rt_type($1),  1) ; }
  | T0YPEMINUS                          { $$ = s0rtpol_make(s0rt_t0ype($1), -1) ; }
  | T0YPEPLUS                           { $$ = s0rtpol_make(s0rt_t0ype($1),  1) ; }
  | VIEWMINUS                           { $$ = s0rtpol_make(s0rt_view($1), -1) ; }
  | VIEWPLUS                            { $$ = s0rtpol_make(s0rt_view($1),  1) ; }
  | VIEWTYPEMINUS                       { $$ = s0rtpol_make(s0rt_viewtype($1), -1) ; }
  | VIEWTYPEPLUS                        { $$ = s0rtpol_make(s0rt_viewtype($1),  1) ; }
  | VIEWT0YPEMINUS                      { $$ = s0rtpol_make(s0rt_viewt0ype($1), -1) ; }
  | VIEWT0YPEPLUS                       { $$ = s0rtpol_make(s0rt_viewt0ype($1),  1) ; }
; /* end of [s0rtpol] */
*)
fun s0rtpol_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0rtpol)
//
val gr = grmrule_append (s0rt)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make($1, 0) ; }")
//
val gr = grmrule_append (PROPMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_prop($1), -1) ; }")
val gr = grmrule_append (PROPPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_prop($1),  1) ; }")
//
val gr = grmrule_append (TYPEMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_type($1), -1) ; }")
val gr = grmrule_append (TYPEPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_type($1),  1) ; }")
//
val gr = grmrule_append (T0YPEMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_t0ype($1), -1) ; }")
val gr = grmrule_append (T0YPEPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_t0ype($1),  1) ; }")
//
val gr = grmrule_append (VIEWMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_view($1), -1) ; }")
val gr = grmrule_append (VIEWPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_view($1),  1) ; }")
//
val gr = grmrule_append (VIEWTYPEMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_viewtype($1), -1) ; }")
val gr = grmrule_append (VIEWTYPEPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_viewtype($1),  1) ; }")
//
val gr = grmrule_append (VIEWT0YPEMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_viewt0ype($1), -1) ; }")
val gr = grmrule_append (VIEWT0YPEPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_viewt0ype($1),  1) ; }")
//
val () = symbol_close (pf | s0rtpol)
//
} // end of [s0rtpol_proc]

(* ****** ****** *)

(*
d0ecarg
  : LBRACE s0quaseq RBRACE              { $$ = $2 ; }
; /* end of [d0ecarg] */
*)

(*
d0ecargseq
  : /* empty */                         { $$ = s0qualstlst_nil() ; }
  | d0ecarg d0ecargseq                  { $$ = s0qualstlst_cons($1, $2) ; }
; /* end of [d0ecargseq] */
*)

fun d0ecargseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecargseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0qualstlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ecarg d0ecargseq))
val () = grmrule_set_action (gr, "{ $$ = s0qualstlst_cons($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (d0ecargseq, SYMREGstar(d0ecarg))
//
val () = symbol_close (pf | d0ecargseq)
//
} // end of [d0ecargseq]

(* ****** ****** *)

(*
semicolonseq
  : /* empty */                         { ; }
  | semicolonseq SEMICOLON              { ; }
; /* end of [semicolonseq] */
*)
fun semicolonseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (semicolonseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! semicolonseq SEMICOLON))
val () = grmrule_set_action (gr, "{ ; }")
//
val () = theGrmrulelst_merge_all (semicolonseq, SYMREGstar(SEMICOLON))
//
val () = symbol_close (pf | semicolonseq)
//
} // end of [semicolonseq_proc]

(* ****** ****** *)

(*
guad0ec_sta
  : e0xp srpthenopt d0ecseq_sta SRPENDIF
                                        { $$ = guad0ec_one($1, $3, $4) ; }
  | e0xp srpthenopt d0ecseq_sta SRPELSE d0ecseq_sta SRPENDIF
                                        { $$ = guad0ec_two($1, $3, $5, $6) ; }
  | e0xp srpthenopt d0ecseq_sta srpelifkind guad0ec_sta
                                        { $$ = guad0ec_cons($1, $3, $4, $5) ; }
; /* end of [guad0ec_sta] */
*)
fun guad0ec_sta_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (guad0ec_sta)
//
val gr = grmrule_append (
  $lst_t {symbol} (tupz! e0xp srpthenopt d0ecseq_sta SRPENDIF)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_one($1, $3, $4) ; }")
//
val gr = grmrule_append ($lst_t {symbol}
  (tupz! e0xp srpthenopt d0ecseq_sta SRPELSE d0ecseq_sta SRPENDIF)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_two($1, $3, $5, $6) ; }")
//
val gr = grmrule_append ($lst_t {symbol}
  (tupz! e0xp srpthenopt d0ecseq_sta srpelifkind guad0ec_sta)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_cons($1, $3, $4, $5) ; }")
//
val () = symbol_close (pf | guad0ec_sta)
//
} // end of [guad0ec_sta_proc]

(* ****** ****** *)

(*
d0ecseq_sta_rev /* tail-recursive */
  : /* empty */                         { $$ = d0ecllst_nil() ; }
  | d0ecseq_sta_rev d0ec_sta semicolonseq
                                        { $$ = d0ecllst_cons($1, $2) ; }
; /* end of [d0ecseq_sta_rev] */
*)
fun d0ecseq_sta_rev_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecseq_sta_rev)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ecseq_sta_rev d0ec_sta semicolonseq))
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_cons($1, $2) ; }")
//
val () = symbol_close (pf | d0ecseq_sta_rev)
//
} // end of [d0ecseq_sta_proc]

(* ****** ****** *)

(*
d0ecseq_sta
  : d0ecseq_sta_rev                     { $$ = d0ecllst_reverse($1) ; }
;
*)
fun d0ecseq_sta_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecseq_sta)
//
val gr = grmrule_append (d0ecseq_sta_rev)
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_reverse($1) ; }")
//
val () = symbol_close (pf | d0ecseq_sta)
//
} // end of [d0ecseq_sta_proc]

(* ****** ****** *)

(*
guad0ec_dyn
  : e0xp srpthenopt d0ecseq_dyn SRPENDIF
                                        { $$ = guad0ec_one($1, $3, $4) ; }
  | e0xp srpthenopt d0ecseq_dyn SRPELSE d0ecseq_dyn SRPENDIF
                                        { $$ = guad0ec_two($1, $3, $5, $6) ; }
  | e0xp srpthenopt d0ecseq_dyn srpelifkind guad0ec_dyn
                                        { $$ = guad0ec_cons($1, $3, $4, $5) ; }
; /* end of [guad0ec_dyn] */
*)

fun guad0ec_dyn_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (guad0ec_dyn)
//
val gr = grmrule_append (
  $lst_t {symbol} (tupz! e0xp srpthenopt d0ecseq_dyn SRPENDIF)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_one($1, $3, $4) ; }")
//
val gr = grmrule_append ($lst_t {symbol}
  (tupz! e0xp srpthenopt d0ecseq_dyn SRPELSE d0ecseq_dyn SRPENDIF)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_two($1, $3, $5, $6) ; }")
//
val gr = grmrule_append ($lst_t {symbol}
  (tupz! e0xp srpthenopt d0ecseq_dyn srpelifkind guad0ec_dyn)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_cons($1, $3, $4, $5) ; }")
//
val () = symbol_close (pf | guad0ec_dyn)
//
} // end of [guad0ec_dyn_proc]

(* ****** ****** *)

(*
d0ecseq_dyn_rev /* tail-recursive */
  : /* empty */                         { $$ = d0ecllst_nil() ; }
  | d0ecseq_dyn_rev d0ec_dyn semicolonseq
                                        { $$ = d0ecllst_cons($1, $2) ; }
; /* end of [d0ecseq_dyn_rev] */
*)
fun d0ecseq_dyn_rev_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecseq_dyn_rev)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ecseq_dyn_rev d0ec_dyn semicolonseq))
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_cons($1, $2) ; }")
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
val gr = grmrule_append (d0ecseq_dyn_rev)
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_reverse($1) ; }")
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
//
  val () = theStartEntry_proc ()
//
  val () = abskind_proc ()
  val () = dcstkind_proc ()
  val () = datakind_proc ()
  val () = stadefkind_proc ()
//
  val () = valkind_proc ()
  val () = funkind_proc ()
//
  val () = lamkind_proc ()
  val () = fixkind_proc ()
//
  val () = srpifkind_proc ()
  val () = srpelifkind_proc ()
  val () = srpthenopt_proc ()
//
  val () = i0de_proc ()
  val () = i0de_dlr_proc ()
  val () = i0deseq_proc ()
  val () = i0dext_proc ()
//
  val () = s0rtid_proc ()
  val () = s0rtpol_proc ()
//
  val () = d0ecargseq_proc ()
//
  val () = semicolonseq_proc ()
//
  val () = guad0ec_sta_proc ()
  val () = d0ecseq_sta_rev_proc ()
  val () = d0ecseq_sta_proc ()
//
  val () = guad0ec_dyn_proc ()
  val () = d0ecseq_dyn_rev_proc () // reversed dynamic declaration sequence
  val () = d0ecseq_dyn_proc ()
//
} // end of [atsgrammar_main]

(* ****** ****** *)

datatype outfmt =
  | OUTFMTyats of ()
  | OUTFMTdesc of ()
  | OUTFMTnone of ()
// end of [outfmt]

fun fprint_usage
  (out: FILEref, cmd: string): void = let
  val () = fprintf (out, "The command [%s] accepts the following flags:\n", @(cmd))
  val () = fprintf (out, "  --help\n", @())
  val () = fprintf (out, "  --format=yats\n", @())
  val () = fprintf (out, "  --format=desc\n", @())
in
  // nothing
end // end of [fprint_usage]

(* ****** ****** *)

implement
main (
  argc, argv
) = () where {
//
  val cmd = "atsgrammar"
//
  var fmt: outfmt = OUTFMTyats()
  val () = loop (argc, argv, 1, fmt) where {
    fun loop {n,i:nat | i <= n} .<n-i>. (
      argc: int n, argv: &(@[string][n]), i: int i, fmt: &outfmt
    ) :<cloref1> void =
    if argc > i then let
      var arg = argv.[i]
    in
      case+ arg of
      | "--help" => let
          val () = fprint_usage (stderr_ref, cmd)
        in
          fmt := OUTFMTnone // loop exits
        end // end of [...]
      | "--format=yats" => (fmt := OUTFMTyats) // loop exits
      | "--format=desc" => (fmt := OUTFMTdesc) // loop exits
      | _ => let
          val () = prerrf ("Warning(atsgrammar): unrecognized flag: %s\n", @(arg))
        in
          loop (argc, argv, i+1, fmt)
        end // end of [_]
    end // end of [if]
  } // end of [val]
//
  val () = atsgrammar_main ()
//
  val () = (case+ fmt of
    | OUTFMTnone () => ()
    | OUTFMTyats () => emit_yats (stdout_ref)
    | OUTFMTdesc () => emit_desc (stdout_ref)
(*
    | _ => let
        val () = prerrf ("Warning(atsgrammar): unrecognized format.\n", @())
      in
        // nothing
      end // end of [_]
*)
  ) : void // end of [val]
//
} // end of [main]

(* ****** ****** *)

(* end of [atsgrammar_main.dats] *)
