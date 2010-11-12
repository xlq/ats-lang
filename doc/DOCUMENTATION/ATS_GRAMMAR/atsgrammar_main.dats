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
dynload "atsgrammar_symbol.dats"
dynload "atsgrammar_grmrule.dats"
//
dynload "atsgrammar_emit_yats.dats"
dynload "atsgrammar_emit_desc.dats"
//
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
  (IDENTIFIER_alp, "ALNUMRIC_IDENTIFIER")
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
val ABSPROP = symbol_make "ABSPROP"
val () = symbol_set_fullname (ABSPROP, "\"absprop\"")
//
val ABSTYPE = symbol_make "ABSTYPE"
val () = symbol_set_fullname (ABSTYPE, "\"abstype\"")
//
val ABST0YPE = symbol_make "ABST0YPE"
val () = symbol_set_fullname (ABST0YPE, "\"abst@ype\"")
//
val ABSVIEW = symbol_make "ABSVIEW"
val () = symbol_set_fullname (ABSVIEW, "\"absview\"")
//
val ABSVIEWTYPE = symbol_make "ABSVIEWTYPE"
val () = symbol_set_fullname (ABSVIEWTYPE, "\"absviewtype\"")
//
val ABSVIEWT0YPE = symbol_make "ABSVIEWT0YPE"
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
val ATLAM = symbol_make "ATLAM"
val () = symbol_set_fullname (ATLAM, "\"@lam\"")
val ATLLAM = symbol_make "ATLLAM"
val () = symbol_set_fullname (ATLLAM, "\"@llam\"")
val ATFIX = symbol_make "ATFIX"
val () = symbol_set_fullname (ATFIX, "\"@fix\"")
//
val BEGIN = symbol_make "BEGIN"
val () = symbol_set_fullname (BEGIN, "\"begin\"")
//
val BREAK = symbol_make "BREAK"
val () = symbol_set_fullname (BREAK, "\"break\"")
//
val CASE = symbol_make "CASE"
val () = symbol_set_fullname (CASE, "\"case\"")
val CASEMINUS = symbol_make "CASEMINUS"
val () = symbol_set_fullname (CASEMINUS, "\"case-\"")
val CASEPLUS = symbol_make "CASEPLUS"
val () = symbol_set_fullname (CASEPLUS, "\"case+\"")
//
val CASTFN = symbol_make "CASTFN"
val () = symbol_set_fullname (CASTFN, "\"castfn\"")
//
val CLASSDEC = symbol_make "CLASSDEC"
val () = symbol_set_fullname (CLASSDEC, "\"classdec\"")
//
val CONTINUE = symbol_make "CONTINUE"
val () = symbol_set_fullname (CONTINUE, "\"continue\"")
//
val DATASORT = symbol_make "DATASORT"
val () = symbol_set_fullname (DATASORT, "\"datasort\"")
val DATAPARASORT = symbol_make "DATAPARASORT"
val () = symbol_set_fullname (DATAPARASORT, "\"dataparasort\"")
//
val DATAPROP = symbol_make "DATAPROP"
val () = symbol_set_fullname (DATAPROP, "\"dataprop\"")
val DATATYPE = symbol_make "DATATYPE"
val () = symbol_set_fullname (DATATYPE, "\"datatype\"")
val DATAVIEW = symbol_make "DATAVIEW"
val () = symbol_set_fullname (DATAVIEW, "\"dataview\"")
val DATAVIEWTYPE = symbol_make "DATAVIEWTYPE"
val () = symbol_set_fullname (DATAVIEWTYPE, "\"dataviewtype\"")
//
val DO = symbol_make "DO"
val () = symbol_set_fullname (DO, "\"do\"")
//
val DYN = symbol_make "DYN"
val () = symbol_set_fullname (DYN, "\"dyn\"")
//
val DYNLOAD = symbol_make "DYNLOAD"
val () = symbol_set_fullname (DYNLOAD, "\"dynload\"")
//
val ELSE = symbol_make "ELSE"
val () = symbol_set_fullname (ELSE, "\"else\"")
//
val END = symbol_make "END"
val () = symbol_set_fullname (END, "\"end\"")
//
val EXCEPTION = symbol_make "EXCEPTION"
val () = symbol_set_fullname (EXCEPTION, "\"exception\"")
//
val EXTERN = symbol_make "EXTERN"
val () = symbol_set_fullname (EXTERN, "\"extern\"")
//
val FIX = symbol_make "FIX"
val () = symbol_set_fullname (FIX, "\"fix\"")
//
val FN = symbol_make "FN"
val () = symbol_set_fullname (FN, "\"fn\"")
val FNSTAR = symbol_make "FNSTAR"
val () = symbol_set_fullname (FNSTAR, "\"fn*\"")
//
val FOR = symbol_make "FOR"
val () = symbol_set_fullname (FOR, "\"for\"")
val FORSTAR = symbol_make "FORSTAR"
val () = symbol_set_fullname (FORSTAR, "\"for*\"")
//
val FUN = symbol_make "FUN"
val () = symbol_set_fullname (FUN, "\"fun\"")
//
val IF = symbol_make "IF"
val () = symbol_set_fullname (IF, "\"if\"")
//
val IMPLEMENT = symbol_make "IMPLEMENT"
val () = symbol_set_fullname (IMPLEMENT, "\"implement\"")
//
val IN = symbol_make "IN"
val () = symbol_set_fullname (IN, "\"in\"")
//
val INFIX = symbol_make "INFIX"
val () = symbol_set_fullname (INFIX, "\"infix\"")
val INFIXL = symbol_make "INFIXL"
val () = symbol_set_fullname (INFIXL, "\"infixl\"")
val INFIXR = symbol_make "INFIXR"
val () = symbol_set_fullname (INFIXR, "\"infixr\"")
//
val LAM = symbol_make "LAM"
val () = symbol_set_fullname (LAM, "\"lam\"")
//
val LET = symbol_make "LET"
val () = symbol_set_fullname (LET, "\"let\"")
//
val LLAM = symbol_make "LLAM"
val () = symbol_set_fullname (LLAM, "\"llam\"")
//
val LOCAL = symbol_make "LOCAL"
val () = symbol_set_fullname (LOCAL, "\"local\"")
//
val MACDEF = symbol_make "MACDEF"
val () = symbol_set_fullname (MACDEF, "\"macdef\"")
val MACRODEF = symbol_make "MACRODEF"
val () = symbol_set_fullname (MACRODEF, "\"macrodef\"")
//
val NONFIX = symbol_make "NONFIX"
val () = symbol_set_fullname (NONFIX, "\"nonfix\"")
//
val OF = symbol_make "OF"
val () = symbol_set_fullname (OF, "\"of\"")
//
val OP = symbol_make "OP"
val () = symbol_set_fullname (OP, "\"op\"")
//
val OVERLOAD = symbol_make "OVERLOAD"
val () = symbol_set_fullname (OVERLOAD, "\"overload\"")
//
val PAR = symbol_make "PAR"
val () = symbol_set_fullname (PAR, "\"par\"")
//
val POSTFIX = symbol_make "POSTFIX"
val () = symbol_set_fullname (POSTFIX, "\"postfix\"")
//
val PRAXI = symbol_make "PRAXI"
val () = symbol_set_fullname (PRAXI, "\"praxi\"")
//
val PRFN = symbol_make "PRFN"
val () = symbol_set_fullname (PRFN, "\"prfn\"")
//
val PRFUN = symbol_make "PRFUN"
val () = symbol_set_fullname (PRFUN, "\"prfun\"")
//
val PROPDEF = symbol_make "PROPDEF"
val () = symbol_set_fullname (PROPDEF, "\"propdef\"")
val PROPMINUS = symbol_make "PROPMINUS"
val () = symbol_set_fullname (PROPMINUS, "\"prop-\"")
val PROPPLUS = symbol_make "PROPPLUS"
val () = symbol_set_fullname (PROPPLUS, "\"prop+\"")
//
val PRVAL = symbol_make "PRVAL"
val () = symbol_set_fullname (PRVAL, "\"prval\"")
//
val REC = symbol_make "REC"
val () = symbol_set_fullname (REC, "\"rec\"")
//
val R0EAD = symbol_make "R0EAD"
val () = symbol_set_fullname (R0EAD, "\"r0ead\"")
//
val SCASE = symbol_make "SCASE"
val () = symbol_set_fullname (SCASE, "\"scase\"")
//
val SIF = symbol_make "SIF"
val () = symbol_set_fullname (SIF, "\"sif\"")
//
val SORTDEF = symbol_make "SORTDEF"
val () = symbol_set_fullname (SORTDEF, "\"sortdef\"")
//
val STA = symbol_make "STA"
val () = symbol_set_fullname (STA, "\"sta\"")
//
val STADEF = symbol_make "STADEF"
val () = symbol_set_fullname (STADEF, "\"stadef\"")
//
val STAIF = symbol_make "STAIF"
val () = symbol_set_fullname (STAIF, "\"staif\"")
//
val STALOAD = symbol_make "STALOAD"
val () = symbol_set_fullname (STALOAD, "\"staload\"")
//
val STAVAR = symbol_make "STAVAR"
val () = symbol_set_fullname (STAVAR, "\"stavar\"")
//
val SYMELIM = symbol_make "SYMELIM"
val () = symbol_set_fullname (SYMELIM, "\"symelim\"")
val SYMINTR = symbol_make "SYMINTR"
val () = symbol_set_fullname (SYMINTR, "\"symintr\"")
//
val THEN = symbol_make "THEN"
val () = symbol_set_fullname (THEN, "\"then\"")
//
val TRY = symbol_make "TRY"
val () = symbol_set_fullname (TRY, "\"try\"")
//
val TYPEDEF = symbol_make "TYPEDEF"
val () = symbol_set_fullname (TYPEDEF, "\"typedef\"")
val TYPEMINUS = symbol_make "TYPEMINUS"
val () = symbol_set_fullname (TYPEMINUS, "\"type-\"")
val TYPEPLUS = symbol_make "TYPEPLUS"
val () = symbol_set_fullname (TYPEPLUS, "\"type+\"")
//
val T0YPE = symbol_make "T0YPE"
val () = symbol_set_fullname (T0YPE, "\"t@ype\"")
val T0YPEMINUS = symbol_make "T0YPEMINUS"
val () = symbol_set_fullname (T0YPEMINUS, "\"t@ype-\"")
val T0YPEPLUS = symbol_make "T0YPEPLUS"
val () = symbol_set_fullname (T0YPEPLUS, "\"t@ype+\"")
//
val VAL = symbol_make "VAL"
val () = symbol_set_fullname (VAL, "\"val\"")
val VALMINUS = symbol_make "VALMINUS"
val () = symbol_set_fullname (VALMINUS, "\"val-\"")
val VALPLUS = symbol_make "VALPLUS"
val () = symbol_set_fullname (VALPLUS, "\"val+\"")
//
val VAR = symbol_make "VAR"
val () = symbol_set_fullname (VAR, "\"var\"")
//
val VIEWDEF = symbol_make "VIEWDEF"
val () = symbol_set_fullname (VIEWDEF, "\"viewdef\"")
val VIEWMINUS = symbol_make "VIEWMINUS"
val () = symbol_set_fullname (VIEWMINUS, "\"view-\"")
val VIEWPLUS = symbol_make "VIEWPLUS"
val () = symbol_set_fullname (VIEWPLUS, "\"view+\"")
//
val VIEWTYPEDEF = symbol_make "VIEWTYPEDEF"
val () = symbol_set_fullname (VIEWTYPEDEF, "\"viewtypedef\"")
val VIEWTYPEMINUS = symbol_make "VIEWTYPEMINUS"
val () = symbol_set_fullname (VIEWTYPEMINUS, "\"viewtype-\"")
val VIEWTYPEPLUS = symbol_make "VIEWTYPEPLUS"
val () = symbol_set_fullname (VIEWTYPEPLUS, "\"viewtype+\"")
//
val VIEWT0YPE = symbol_make "VIEWT0YPE"
val () = symbol_set_fullname (VIEWT0YPE, "\"viewt@ype\"")
val VIEWT0YPEMINUS = symbol_make "VIEWT0YPEMINUS"
val () = symbol_set_fullname (VIEWT0YPEMINUS, "\"viewt@ype-\"")
val VIEWT0YPEPLUS = symbol_make "VIEWT0YPEPLUS"
val () = symbol_set_fullname (VIEWT0YPEPLUS, "\"viewt@ype+\"")
//
val WHEN = symbol_make "WHEN"
val () = symbol_set_fullname (WHEN, "\"when\"")
//
val WHERE = symbol_make "WHERE"
val () = symbol_set_fullname (WHERE, "\"where\"")
//
val WHILE = symbol_make "WHILE"
val () = symbol_set_fullname (WHILE, "\"while\"")
val WHILESTAR = symbol_make "WHILESTAR"
val () = symbol_set_fullname (WHILESTAR, "\"while*\"")
//
val WITH = symbol_make "WITH"
val () = symbol_set_fullname (WITH, "\"with\"")
//
val WITHPROP = symbol_make "WITHPROP"
val () = symbol_set_fullname (WITHPROP, "\"withprop\"")
val WITHTYPE = symbol_make "WITHTYPE"
val () = symbol_set_fullname (WITHTYPE, "\"withtype\"")
val WITHVIEW = symbol_make "WITHVIEW"
val () = symbol_set_fullname (WITHVIEW, "\"withview\"")
val WITHVIEWTYPE = symbol_make "WITHVIEWTYPE"
val () = symbol_set_fullname (WITHVIEWTYPE, "\"withviewtype\"")
//
(* ****** ****** *)
//
val AMPERSAND = symbol_make ("AMPERSAND")
val () = symbol_set_fullname (AMPERSAND, "\"&\"")
//
val BACKQUOTE = symbol_make ("BACKQUOTE")
val () = symbol_set_fullname (BACKQUOTE, "\"`\"")
//
val BACKSLASH = symbol_make ("BACKSLASH")
val () = symbol_set_fullname (BACKSLASH, "\"\\\"")
//
val BANG = symbol_make ("BANG")
val () = symbol_set_fullname (BANG, "\"!\"")
//
val BAR = symbol_make ("BAR")
val () = symbol_set_fullname (BAR, "\"|\"")
//
val COMMA = symbol_make ("COMMA")
val () = symbol_set_fullname (COMMA, "\",\"")
//
val COLON = symbol_make ("COLON")
val () = symbol_set_fullname (COLON, "\":\"")
//
val SEMICOLON = symbol_make ("SEMICOLON")
val () = symbol_set_fullname (SEMICOLON, "\";\"")
//
val DOT = symbol_make ("DOT")
val () = symbol_set_fullname (DOT, "\".\"")
//
val EQ = symbol_make ("EQ")
val () = symbol_set_fullname (EQ, "\"=\"")
//
val LT = symbol_make ("LT")
val () = symbol_set_fullname (LT, "\"<\"")
val GT = symbol_make ("GT")
val () = symbol_set_fullname (GT, "\">\"")
//
val DOLLAR = symbol_make ("DOLLAR")
val () = symbol_set_fullname (DOLLAR, "\"$\"")
//
val HASH = symbol_make ("HASH")
val () = symbol_set_fullname (HASH, "\"#\"")
//
val TILDA = symbol_make ("TILDA")
val () = symbol_set_fullname (TILDA, "\"~\"")
//
val DOTDOT = symbol_make ("DOTDOT")
val () = symbol_set_fullname (DOTDOT, "\"..\"")
val DOTDOTDOT = symbol_make ("DOTDOTDOT")
val () = symbol_set_fullname (DOTDOTDOT, "\"...\"")
//
val EQLT = symbol_make ("EQLT")
val () = symbol_set_fullname (EQLT, "\"=<\"")
val EQGT = symbol_make ("EQGT")
val () = symbol_set_fullname (EQGT, "\"=>\"")
val EQLTGT = symbol_make ("EQLTGT")
val () = symbol_set_fullname (EQLTGT, "\"=<>\"")
val EQGTGT = symbol_make ("EQGTGT")
val () = symbol_set_fullname (EQGTGT, "\"=>>\"")
//
val EQSLASHEQGT = symbol_make ("EQSLASHEQGT")
val () = symbol_set_fullname (EQSLASHEQGT, "\"=/=>\"")
val EQSLASHEQGTGT = symbol_make ("EQSLASHEQGTGT")
val () = symbol_set_fullname (EQSLASHEQGTGT, "\"=/=>>\"")
//
val GTLT = symbol_make ("GTLT")
val () = symbol_set_fullname (GTLT, "\"<>\"")
//
val DOTLT = symbol_make ("DOTLT")
val () = symbol_set_fullname (DOTLT, "\".<\"")
val GTDOT = symbol_make ("GTDOT")
val () = symbol_set_fullname (GTDOT, "\">.\"")
val DOTLTGTDOT = symbol_make ("DOTLTGTDOT")
val () = symbol_set_fullname (DOTLTGTDOT, "\".<>.\"")
//
val MINUSLT = symbol_make ("MINUSLT")
val () = symbol_set_fullname (MINUSLT, "\"-<\"")
val MINUSGT = symbol_make ("MINUSGT")
val () = symbol_set_fullname (MINUSGT, "\"->\"")
val MINUSLTGT = symbol_make ("MINUSLTGT")
val () = symbol_set_fullname (MINUSLTGT, "\"-<>\"")
//
val COLONLT = symbol_make ("COLONLT")
val () = symbol_set_fullname (COLONLT, "\":<\"")
val COLONLTGT = symbol_make ("COLONLTGT")
val () = symbol_set_fullname (COLONLTGT, "\":<>\"")
//
val BACKQUOTELPAREN = symbol_make ("BACKQUOTELPAREN")
val () = symbol_set_fullname (BACKQUOTELPAREN, "\"`(\"")
val COMMALPAREN = symbol_make ("COMMALPAREN")
val () = symbol_set_fullname (COMMALPAREN, "\",(\"")
val PERCENTLPAREN = symbol_make ("PERCENTLPAREN")
val () = symbol_set_fullname (PERCENTLPAREN, "\"%(\"")
(*
//
// HX: these symbols were reserved for supporting MP
//
val BACKQUOTELBRACKET = symbol_make ("BACKQUOTELBRACKET")
val () = symbol_set_fullname (BACKQUOTELBRACKET, "\"`[\"")
val PERCENTLBRACKET = symbol_make ("PERCENTLBRACKET")
val () = symbol_set_fullname (COMMALBRACE, "\"%[\"")
val COMMALBRACKET = symbol_make ("COMMALBRACKET")
val () = symbol_set_fullname (COMMALBRACKET, "\",[\"")
//
val BACKQUOTELBRACE = symbol_make ("BACKQUOTELBRACE")
val () = symbol_set_fullname (BACKQUOTELBRACE, "\"`{\"")
val PERCENTLBRACE = symbol_make ("PERCENTLBRACE")
val () = symbol_set_fullname (COMMALBRACE, "\"%{\"")
val COMMALBRACE = symbol_make ("COMMALBRACE")
val () = symbol_set_fullname (COMMALBRACE, "\",{\"")
*)
(* ****** ****** *)
//
val DLRARRSZ = symbol_make "DLRARRSZ"
val () = symbol_set_fullname (DLRARRSZ, "\"$arrsz\"")
//
val DLRLST_T = symbol_make "DLRLST_T"
val () = symbol_set_fullname (DLRLST_T, "\"$lst_t\"")
val DLRLST_VT = symbol_make "DLRLST_VT"
val () = symbol_set_fullname (DLRLST_VT, "\"$lst_vt\"")
//
val DLRREC_T = symbol_make "DLRREC_T"
val () = symbol_set_fullname (DLRREC_T, "\"$rec_t\"")
val DLRREC_VT = symbol_make "DLRREC_VT"
val () = symbol_set_fullname (DLRREC_VT, "\"$rec_vt\"")
//
val DLRTUP_T = symbol_make "DLRTUP_T"
val () = symbol_set_fullname (DLRTUP_T, "\"$tup_t\"")
val DLRTUP_VT = symbol_make "DLRTUP_VT"
val () = symbol_set_fullname (DLRTUP_VT, "\"$tup_vt\"")
//
val DLRDELAY = symbol_make "DLRDELAY"
val () = symbol_set_fullname (DLRDELAY, "\"$delay\"")
val DLRLDELAY = symbol_make "DLRLDELAY"
val () = symbol_set_fullname (DLRLDELAY, "\"$ldelay\"")
//
val DLRDYNLOAD = symbol_make "DLRDYNLOAD"
val () = symbol_set_fullname (DLRDYNLOAD, "\"$dynload\"")
//
val DLREFFMASK_ALL = symbol_make "DLREFFMASK_ALL"
val () = symbol_set_fullname (DLREFFMASK_ALL, "\"$effmask_all\"")
val DLREFFMASK_EXN = symbol_make "DLREFFMASK_EXN"
val () = symbol_set_fullname (DLREFFMASK_EXN, "\"$effmask_exn\"")
val DLREFFMASK_NTM = symbol_make "DLREFFMASK_NTM"
val () = symbol_set_fullname (DLREFFMASK_NTM, "\"$effmask_ntm\"")
val DLREFFMASK_REF = symbol_make "DLREFFMASK_REF"
val () = symbol_set_fullname (DLREFFMASK_REF, "\"$effmask_ref\"")
//
val DLRDECRYPT = symbol_make "DLRDECRYPT"
val () = symbol_set_fullname (DLRDECRYPT, "\"$decrypt\"")
val DLRENCRYPT = symbol_make "DLRENCRYPT"
val () = symbol_set_fullname (DLRENCRYPT, "\"$encrypt\"")
//
val DLREXTERN = symbol_make "DLREXTERN"
val () = symbol_set_fullname (DLREXTERN, "\"$extern\"")
val DLREXTVAL = symbol_make "DLREXTVAL"
val () = symbol_set_fullname (DLREXTVAL, "\"$extval\"")
//
val DLREXTYPE = symbol_make "DLREXTYPE"
val () = symbol_set_fullname (DLREXTYPE, "\"$extype\"")
val DLREXTYPE_STRUCT = symbol_make "DLREXTYPE_STRUCT"
val () = symbol_set_fullname (DLREXTYPE_STRUCT, "\"$extype_struct\"")
//
val DLRFOLD = symbol_make "DLRFOLD"
val () = symbol_set_fullname (DLRFOLD, "\"$fold\"")
val DLRUNFOLD = symbol_make "DLRUNFOLD"
val () = symbol_set_fullname (DLRUNFOLD, "\"$unfold\"")
//
val DLRRAISE = symbol_make "DLRRAISE"
val () = symbol_set_fullname (DLRRAISE, "\"$raise\"")
//
val DLRTYPEOF = symbol_make "DLRTYPEOF"
val () = symbol_set_fullname (DLRTYPEOF, "\"$typeof\"")
//
(* ****** ****** *)
//
val SRPFILENAME = symbol_make "SRPFILENAME"
val () = symbol_set_fullname (SRPFILENAME, "\"#FILENAME\"")
val SRPLOCATION = symbol_make "SRPLOCATION"
val () = symbol_set_fullname (SRPLOCATION, "\"#LOCATION\"")
val SRPCHARCOUNT = symbol_make "SRPCHARCOUNT"
val () = symbol_set_fullname (SRPCHARCOUNT, "\"#CHARCOUNT\"")
val SRPLINECOUNT = symbol_make "SRPLINECOUNT"
val () = symbol_set_fullname (SRPLINECOUNT, "\"#LINECOUNT\"")
//
val SRPASSERT = symbol_make "SRPASSERT"
val () = symbol_set_fullname (SRPASSERT, "\"#assert\"")
val SRPDEFINE = symbol_make "SRPDEFINE"
val () = symbol_set_fullname (SRPDEFINE, "\"#define\"")
val SRPELSE = symbol_make "SRPELSE"
val () = symbol_set_fullname (SRPELSE, "\"#else\"")
val SRPELIF = symbol_make "SRPELIF"
val () = symbol_set_fullname (SRPELIF, "\"#elif\"")
val SRPELIFDEF = symbol_make "SRPELIFDEF"
val () = symbol_set_fullname (SRPELIFDEF, "\"#elifdef\"")
val SRPELIFNDEF = symbol_make "SRPELIFNDEF"
val () = symbol_set_fullname (SRPELIFNDEF, "\"#elifndef\"")
val SRPENDIF = symbol_make "SRPENDIF"
val () = symbol_set_fullname (SRPENDIF, "\"#endif\"")
val SRPERROR = symbol_make "SRPERROR"
val () = symbol_set_fullname (SRPERROR, "\"#error\"")
val SRPIF = symbol_make "SRPIF"
val () = symbol_set_fullname (SRPIF, "\"#if\"")
val SRPIFDEF = symbol_make "SRPIFDEF"
val () = symbol_set_fullname (SRPIFDEF, "\"#ifdef\"")
val SRPIFNDEF = symbol_make "SRPIFNDEF"
val () = symbol_set_fullname (SRPIFNDEF, "\"#ifndef\"")
val SRPINCLUDE = symbol_make "SRPINCLUDE"
val () = symbol_set_fullname (SRPINCLUDE, "\"#include\"")
val SRPPRINT = symbol_make "SRPPRINT"
val () = symbol_set_fullname (SRPPRINT, "\"#print\"")
val SRPTHEN = symbol_make "SRPTHEN"
val () = symbol_set_fullname (SRPTHEN, "\"#then\"")
val SRPUNDEF = symbol_make "SRPUNDEF"
val () = symbol_set_fullname (SRPUNDEF, "\"#undef\"")
//
(* ****** ****** *)
//
val FOLDAT = symbol_make "FOLDAT"
val () = symbol_set_fullname (FOLDAT, "\"fold@\"")
val FREEAT = symbol_make "FREEAT"
val () = symbol_set_fullname (FREEAT, "\"free@\"")
val VIEWAT = symbol_make "VIEWAT"
val () = symbol_set_fullname (VIEWAT, "\"view@\"")
//
(* ****** ****** *)

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
val i0deseq = symbol_make_nt "i0deseq"

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
val () = theGrmrulelst_merge_all (i0deseq, SYMREGopt(SRPTHEN))
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

fun i0deseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (i0deseq)
//
val gr = grmrule_append ()
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de i0deseq))
//
val () = theGrmrulelst_merge_all (i0deseq, SYMREGstar(i0de))
//
val () = symbol_close (pf | i0deseq)
//
} // end of [i0deseq_proc]

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
  val () = i0deseq_proc ()
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

implement
main () = () where {
//
  val () = atsgrammar_main ()
//
  val () = emit_symdefall_yats (stdout_ref)
//
  val () = emit_symdefall_desc (stdout_ref)
//
} // end of [main]

(* ****** ****** *)

(* end of [atsgrammar_main.dats] *)
