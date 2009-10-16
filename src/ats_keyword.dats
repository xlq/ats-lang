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

// Time: July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* ats_keyword: handling keywords in ATS *)

(* ****** ****** *)

staload "ats_lexer.sats"

(* ****** ****** *)

staload "ats_keyword.sats"

(* ****** ****** *)

%{^

#include "ats_grammar_yats.h"

typedef
struct {
  char *key ; int val ;
} keyval ;

#define ATS_KEYWORD_TABLE_SIZE 1024

keyval // a global variable
ats_keyword_table[ATS_KEYWORD_TABLE_SIZE] = {0} ;

static
ats_void_type
ats_keyval_insert (
  char *key, int val
) {
  unsigned int hash_val ; int i ; keyval *itm ;

  hash_val = atspre_string_hash_33 ((char*)key) ;
  i = hash_val % ATS_KEYWORD_TABLE_SIZE ; itm = &ats_keyword_table[i] ;

  while (itm->key) {
    i += 1 ; if (i == ATS_KEYWORD_TABLE_SIZE) i = 0 ;
    itm = &ats_keyword_table[i] ;
  }
  itm->key = (char*)key ; itm->val = (int)val ;
  return ;
}

ats_int_type
ats_keyword_search (ats_ptr_type key) {
  unsigned int hash_val ; int i ; keyval *itm ;

  hash_val = atspre_string_hash_33 (key) ;
  i = hash_val % ATS_KEYWORD_TABLE_SIZE ; itm = &ats_keyword_table[i] ;

  while (itm->key) {
    if (!strcmp((char*)key, itm->key)) return itm->val ;
    i += 1 ; if (i == ATS_KEYWORD_TABLE_SIZE) i = 0 ;
    itm = &ats_keyword_table[i] ;
  }
  return -1 ;
}

static inline
ats_void_type
ats_keyval_table_init (
  // there no argument for this function
) {

/* symbolic keywords */
ats_keyval_insert("&", AMPERSAND) ;
ats_keyval_insert("`", BACKQUOTE) ;
ats_keyval_insert("!", BANG) ;
ats_keyval_insert("|", BAR) ;
ats_keyval_insert(":", COLON) ;
ats_keyval_insert("$", DOLLAR) ;
ats_keyval_insert(".", DOT) ;
ats_keyval_insert("=", EQ) ;
ats_keyval_insert("#", HASH) ;
ats_keyval_insert("~", TILDA) ;
ats_keyval_insert("..", DOTDOT) ;
ats_keyval_insert("...", DOTDOTDOT) ;
ats_keyval_insert("=>", EQGT) ; // implication without decoration
ats_keyval_insert("=<", EQLT) ; // implication decoration
ats_keyval_insert("=<>", EQLTGT) ; // implication with empty decoration
ats_keyval_insert("=/=>", EQSLASHEQGT) ;
ats_keyval_insert("=>>", EQGTGT) ;
ats_keyval_insert("=/=>>", EQSLASHEQGTGT) ;
ats_keyval_insert("<", LT) ;
ats_keyval_insert(">", GT) ;
ats_keyval_insert("><", GTLT) ;
ats_keyval_insert(".<", DOTLT) ;
ats_keyval_insert(">.", GTDOT) ; // .<...>. : metric
ats_keyval_insert(".<>.", DOTLTGTDOT) ;
ats_keyval_insert("->", MINUSGT) ; // implication
ats_keyval_insert("-<", MINUSLT) ; // -<...> : decorated implication
ats_keyval_insert("-<>", MINUSLTGT) ;
ats_keyval_insert(":<", COLONLT) ; // :<...> : decorated implication
ats_keyval_insert(":<>", COLONLTGT) ;

/* alphanumeric keywords */
ats_keyval_insert("absprop", ABSPROP) ;
ats_keyval_insert("abstype", ABSTYPE) ;
ats_keyval_insert("abst@ype", ABST0YPE) ;
ats_keyval_insert("absview", ABSVIEW) ;
ats_keyval_insert("absviewtype", ABSVIEWTYPE) ;
ats_keyval_insert("absviewt@ype", ABSVIEWT0YPE) ;
ats_keyval_insert("and", AND) ;
ats_keyval_insert("arrvar", ARRVAR) ;
ats_keyval_insert("as", AS) ;
ats_keyval_insert("assume", ASSUME) ;
ats_keyval_insert("begin", BEGIN) ;
ats_keyval_insert("break", BREAK) ;
ats_keyval_insert("case", CASE) ;
ats_keyval_insert("castfn", CASTFN) ; // for casting functions
ats_keyval_insert("class", CLASS) ;
ats_keyval_insert("continue", CONTINUE) ;
ats_keyval_insert("datasort", DATASORT) ;
ats_keyval_insert("dataparasort", DATAPARASORT) ;
ats_keyval_insert("dataprop", DATAPROP) ;
ats_keyval_insert("datatype", DATATYPE) ;
ats_keyval_insert("dataview", DATAVIEW) ;
ats_keyval_insert("dataviewtype", DATAVIEWTYPE) ;
ats_keyval_insert("dyn", DYN) ;
ats_keyval_insert("dynload", DYNLOAD) ;
ats_keyval_insert("else", ELSE) ;
ats_keyval_insert("end", END) ;
ats_keyval_insert("exception", EXCEPTION) ;
ats_keyval_insert("extern", EXTERN) ;
ats_keyval_insert("fix", FIX) ;
ats_keyval_insert("fn", FN) ;
ats_keyval_insert("for", FOR) ;
ats_keyval_insert("fun", FUN) ;
ats_keyval_insert("if", IF) ;
ats_keyval_insert("implement", IMPLEMENT) ;
ats_keyval_insert("in", IN) ;
ats_keyval_insert("infix", INFIX) ;
ats_keyval_insert("infixl", INFIXL) ;
ats_keyval_insert("infixr", INFIXR) ;
ats_keyval_insert("lam", LAM) ;
ats_keyval_insert("let", LET) ;
ats_keyval_insert("llam", LLAM) ;
ats_keyval_insert("local", LOCAL) ;
ats_keyval_insert("macdef", MACDEF) ;
ats_keyval_insert("macrodef", MACRODEF) ;
ats_keyval_insert("method", METHOD) ;
ats_keyval_insert("module", MODULE) ;
ats_keyval_insert("nonfix", NONFIX) ;
ats_keyval_insert("object", OBJECT) ;
ats_keyval_insert("overload", OVERLOAD) ;
ats_keyval_insert("par", PAR) ;
ats_keyval_insert("postfix", POSTFIX) ;
ats_keyval_insert("praxi", PRAXI) ;
ats_keyval_insert("prefix", PREFIX) ;
ats_keyval_insert("prfn", PRFN) ;
ats_keyval_insert("prfun", PRFUN) ;
ats_keyval_insert("prval", PRVAL) ;
ats_keyval_insert("of", OF) ;
ats_keyval_insert("op", OP) ;
ats_keyval_insert("propdef", PROPDEF) ;
ats_keyval_insert("rec", REC) ;
ats_keyval_insert("scase", SCASE) ;
ats_keyval_insert("sif", SIF) ;
ats_keyval_insert("sortdef", SORTDEF) ;
ats_keyval_insert("sta", STA) ;
ats_keyval_insert("stadef", STADEF) ;
ats_keyval_insert("staif", STAIF) ;
ats_keyval_insert("staload", STALOAD) ;
ats_keyval_insert("stavar", STAVAR) ;
ats_keyval_insert("struct", STRUCT) ;
ats_keyval_insert("super", SUPER) ;
ats_keyval_insert("symelim", SYMELIM) ;
ats_keyval_insert("symintr", SYMINTR) ;
ats_keyval_insert("then", THEN) ;
ats_keyval_insert("try", TRY) ;
ats_keyval_insert("typedef", TYPEDEF) ;
ats_keyval_insert("union", UNION) ;
ats_keyval_insert("val", VAL) ;
ats_keyval_insert("var", VAR) ;
ats_keyval_insert("viewdef", VIEWDEF) ;
ats_keyval_insert("viewtypedef", VIEWTYPEDEF) ;
ats_keyval_insert("when", WHEN) ;
ats_keyval_insert("where", WHERE) ;
ats_keyval_insert("while", WHILE) ;
ats_keyval_insert("with", WITH) ;
ats_keyval_insert("withprop", WITHPROP) ;
ats_keyval_insert("withtype", WITHTYPE) ;
ats_keyval_insert("withview", WITHVIEW) ;
ats_keyval_insert("withviewtype", WITHVIEWTYPE) ;

ats_keyval_insert("$arrsz", DLRARRSZ) ;
ats_keyval_insert("$effmask_all", DLREFFMASK_ALL) ;
ats_keyval_insert("$effmask_exn", DLREFFMASK_EXN) ;
ats_keyval_insert("$effmask_ntm", DLREFFMASK_NTM) ;
ats_keyval_insert("$effmask_ref", DLREFFMASK_REF) ;
ats_keyval_insert("$exec", DLREXEC) ;
ats_keyval_insert("$extern", DLREXTERN) ;
ats_keyval_insert("$extval", DLREXTVAL) ;
ats_keyval_insert("$extype", DLREXTYPE) ;
ats_keyval_insert("$decrypt", DLRDECRYPT) ;
ats_keyval_insert("$delay", DLRDELAY) ;
ats_keyval_insert("$delay_vt", DLRDELAY_VT) ;
ats_keyval_insert("$dynload", DLRDYNLOAD) ;
ats_keyval_insert("$encrypt", DLRENCRYPT) ;
ats_keyval_insert("$fold", DLRFOLD) ;
ats_keyval_insert("$lst", DLRLST_T) ;
ats_keyval_insert("$lst_t", DLRLST_T) ;
ats_keyval_insert("$lst_vt", DLRLST_VT) ;
ats_keyval_insert("$obj", DLROBJ_T) ;
ats_keyval_insert("$obj_t", DLROBJ_T) ;
ats_keyval_insert("$obj_vt", DLROBJ_VT) ;
ats_keyval_insert("$objmod", DLROBJMOD) ;
ats_keyval_insert("$raise", DLRRAISE) ;
ats_keyval_insert("$rec_t", DLRREC_T) ;
ats_keyval_insert("$rec_vt", DLRREC_VT) ;
ats_keyval_insert("$spawn", DLRSPAWN) ;
ats_keyval_insert("$tup_t", DLRTUP_T) ;
ats_keyval_insert("$tup_vt", DLRTUP_VT) ;
ats_keyval_insert("$typeof", DLRTYPEOF) ;
ats_keyval_insert("$unfold", DLRUNFOLD) ;

ats_keyval_insert("#assert", SRPASSERT) ;
ats_keyval_insert("#define", SRPDEFINE) ;
ats_keyval_insert("#elif", SRPELIF) ;
ats_keyval_insert("#elifdef", SRPELIFDEF) ;
ats_keyval_insert("#elifndef", SRPELIFNDEF) ;
ats_keyval_insert("#else", SRPELSE) ;
ats_keyval_insert("#endif", SRPENDIF) ;
ats_keyval_insert("#error", SRPERROR) ;
ats_keyval_insert("#if", SRPIF) ;
ats_keyval_insert("#ifdef", SRPIFDEF) ;
ats_keyval_insert("#ifndef", SRPIFNDEF) ;
ats_keyval_insert("#include", SRPINCLUDE) ;
ats_keyval_insert("#then", SRPTHEN) ;
ats_keyval_insert("#print", SRPPRINT) ;

ats_keyval_insert("#FILENAME", SRPFILENAME) ;
ats_keyval_insert("#LOCATION", SRPLOCATION) ;
ats_keyval_insert("#CHARCOUNT", SRPCHARCOUNT) ;
ats_keyval_insert("#LINECOUNT", SRPLINECOUNT) ;

ats_keyval_insert("fold@", FOLDAT) ;
ats_keyval_insert("free@", FREEAT) ;
ats_keyval_insert("view@", VIEWAT) ;

ats_keyval_insert("r@ead", R0EAD) ;

ats_keyval_insert("t@ype", T0YPE) ;
ats_keyval_insert("t@ype+", T0YPEPLUS) ;
ats_keyval_insert("t@ype-", T0YPEMINUS) ;
ats_keyval_insert("viewt@ype", VIEWT0YPE) ;
ats_keyval_insert("viewt@ype+", VIEWT0YPEPLUS) ;
ats_keyval_insert("viewt@ype-", VIEWT0YPEMINUS) ;
ats_keyval_insert("abst@ype", ABST0YPE) ;
ats_keyval_insert("absviewt@ype", ABSVIEWT0YPE) ;

}

%}

extern fun keyval_table_init (): void = "ats_keyval_table_init"

(* ****** ****** *)

val () = keyval_table_init () // initializing the keyword table

(* ****** ****** *)

(* end of [ats_keyword.dats] *)
