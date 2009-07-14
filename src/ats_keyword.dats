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

typedef struct {
  ats_ptr_type key ;
  ats_int_type val ;
} keyval ;

#define ATS_KEYWORD_TABLE_SIZE 1024

keyval ats_keyword_table[ATS_KEYWORD_TABLE_SIZE] =
  { { (ats_ptr_type)0, 0 } } ;

static ats_void_type
keyval_insert (ats_ptr_type key, ats_int_type val) {
  unsigned int hash_val ; int i ; keyval *itm ;

  hash_val = atspre_string_hash_33 ((char *)key) ;
  i = hash_val % ATS_KEYWORD_TABLE_SIZE ;
  itm = ats_keyword_table + i ;

  while (itm->key) {
    ++i ;
    if (i == ATS_KEYWORD_TABLE_SIZE) i = 0 ;
    itm = ats_keyword_table + i ;
  }

  itm->key = key ; itm->val = val ;
  return ;
}

ats_int_type keyword_search (ats_ptr_type key) {
  unsigned int hash_val ; int i ; keyval *itm ;

  hash_val = atspre_string_hash_33 ((char *)key) ;
  i = hash_val % ATS_KEYWORD_TABLE_SIZE ;
  itm = ats_keyword_table + i ;

  while (itm->key) {
    if (strcmp ((char*)key, itm->key) == 0) {
      return itm->val ;
    }
    ++i ;
    if (i == ATS_KEYWORD_TABLE_SIZE) i = 0 ;
    itm = ats_keyword_table + i ;
  }

  return -1 ;
}

static inline
ats_void_type keyval_table_init () {

/* symbolic keywords */
keyval_insert("&", AMPERSAND) ;
keyval_insert("`", BACKQUOTE) ;
keyval_insert("!", BANG) ;
keyval_insert("|", BAR) ;
keyval_insert(":", COLON) ;
keyval_insert("$", DOLLAR) ;
keyval_insert(".", DOT) ;
keyval_insert("=", EQ) ;
keyval_insert("#", HASH) ;
keyval_insert("~", TILDA) ;
keyval_insert("..", DOTDOT) ;
keyval_insert("...", DOTDOTDOT) ;
keyval_insert("=>", EQGT) ; // implication without decoration
keyval_insert("=<", EQLT) ; // implication decoration
keyval_insert("=<>", EQLTGT) ; // implication with empty decoration
keyval_insert("=/=>", EQSLASHEQGT) ;
keyval_insert("=>>", EQGTGT) ;
keyval_insert("=/=>>", EQSLASHEQGTGT) ;
keyval_insert("<", LT) ;
keyval_insert(">", GT) ;
keyval_insert("><", GTLT) ;
keyval_insert(".<", DOTLT) ;
keyval_insert(">.", GTDOT) ; // .<...>. : metric
keyval_insert(".<>.", DOTLTGTDOT) ;
keyval_insert("->", MINUSGT) ; // implication
keyval_insert("-<", MINUSLT) ; // -<...> : decorated implication
keyval_insert("-<>", MINUSLTGT) ;
keyval_insert(":<", COLONLT) ; // :<...> : decorated implication
keyval_insert(":<>", COLONLTGT) ;

/* alphanumeric keywords */
keyval_insert("absprop", ABSPROP) ;
keyval_insert("abstype", ABSTYPE) ;
keyval_insert("abst@ype", ABST0YPE) ;
keyval_insert("absview", ABSVIEW) ;
keyval_insert("absviewtype", ABSVIEWTYPE) ;
keyval_insert("absviewt@ype", ABSVIEWT0YPE) ;
keyval_insert("and", AND) ;
keyval_insert("arrvar", ARRVAR) ;
keyval_insert("as", AS) ;
keyval_insert("assume", ASSUME) ;
keyval_insert("begin", BEGIN) ;
keyval_insert("break", BREAK) ;
keyval_insert("case", CASE) ;
keyval_insert("castfn", CASTFN) ; // for casting functions
keyval_insert("class", CLASS) ;
keyval_insert("continue", CONTINUE) ;
keyval_insert("datasort", DATASORT) ;
keyval_insert("dataparasort", DATAPARASORT) ;
keyval_insert("dataprop", DATAPROP) ;
keyval_insert("datatype", DATATYPE) ;
keyval_insert("dataview", DATAVIEW) ;
keyval_insert("dataviewtype", DATAVIEWTYPE) ;
keyval_insert("dyn", DYN) ;
keyval_insert("dynload", DYNLOAD) ;
keyval_insert("else", ELSE) ;
keyval_insert("end", END) ;
keyval_insert("exception", EXCEPTION) ;
keyval_insert("extern", EXTERN) ;
keyval_insert("fix", FIX) ;
keyval_insert("fn", FN) ;
keyval_insert("for", FOR) ;
keyval_insert("fun", FUN) ;
keyval_insert("if", IF) ;
keyval_insert("implement", IMPLEMENT) ;
keyval_insert("in", IN) ;
keyval_insert("infix", INFIX) ;
keyval_insert("infixl", INFIXL) ;
keyval_insert("infixr", INFIXR) ;
keyval_insert("lam", LAM) ;
keyval_insert("let", LET) ;
keyval_insert("llam", LLAM) ;
keyval_insert("local", LOCAL) ;
keyval_insert("macdef", MACDEF) ;
keyval_insert("macrodef", MACRODEF) ;
keyval_insert("method", METHOD) ;
keyval_insert("mtdimp", MTDIMP) ;
keyval_insert("nonfix", NONFIX) ;
keyval_insert("overload", OVERLOAD) ;
keyval_insert("par", PAR) ;
keyval_insert("postfix", POSTFIX) ;
keyval_insert("praxi", PRAXI) ;
keyval_insert("prefix", PREFIX) ;
keyval_insert("prfn", PRFN) ;
keyval_insert("prfun", PRFUN) ;
keyval_insert("prval", PRVAL) ;
keyval_insert("of", OF) ;
keyval_insert("op", OP) ;
keyval_insert("propdef", PROPDEF) ;
keyval_insert("rec", REC) ;
keyval_insert("scase", SCASE) ;
keyval_insert("sif", SIF) ;
keyval_insert("sortdef", SORTDEF) ;
keyval_insert("sta", STA) ;
keyval_insert("stadef", STADEF) ;
keyval_insert("staif", STAIF) ;
keyval_insert("staload", STALOAD) ;
keyval_insert("stavar", STAVAR) ;
keyval_insert("struct", STRUCT) ;
keyval_insert("super", SUPER) ;
keyval_insert("symelim", SYMELIM) ;
keyval_insert("symintr", SYMINTR) ;
keyval_insert("then", THEN) ;
keyval_insert("try", TRY) ;
keyval_insert("typedef", TYPEDEF) ;
keyval_insert("union", UNION) ;
keyval_insert("val", VAL) ;
keyval_insert("valimp", VALIMP) ;
keyval_insert("var", VAR) ;
keyval_insert("varimp", VARIMP) ;
keyval_insert("viewdef", VIEWDEF) ;
keyval_insert("viewtypedef", VIEWTYPEDEF) ;
keyval_insert("when", WHEN) ;
keyval_insert("where", WHERE) ;
keyval_insert("while", WHILE) ;
keyval_insert("with", WITH) ;
keyval_insert("withprop", WITHPROP) ;
keyval_insert("withtype", WITHTYPE) ;
keyval_insert("withview", WITHVIEW) ;
keyval_insert("withviewtype", WITHVIEWTYPE) ;

keyval_insert("#assert", SRPASSERT) ;
keyval_insert("#define", SRPDEFINE) ;
keyval_insert("#elif", SRPELIF) ;
keyval_insert("#elifdef", SRPELIFDEF) ;
keyval_insert("#elifndef", SRPELIFNDEF) ;
keyval_insert("#else", SRPELSE) ;
keyval_insert("#endif", SRPENDIF) ;
keyval_insert("#error", SRPERROR) ;
keyval_insert("#if", SRPIF) ;
keyval_insert("#ifdef", SRPIFDEF) ;
keyval_insert("#ifndef", SRPIFNDEF) ;
keyval_insert("#include", SRPINCLUDE) ;
keyval_insert("#then", SRPTHEN) ;
keyval_insert("#print", SRPPRINT) ;

keyval_insert("$arrsz", DLRARRSZ) ;
keyval_insert("$effmask_all", DLREFFMASK_ALL) ;
keyval_insert("$effmask_exn", DLREFFMASK_EXN) ;
keyval_insert("$effmask_ntm", DLREFFMASK_NTM) ;
keyval_insert("$effmask_ref", DLREFFMASK_REF) ;
keyval_insert("$exec", DLREXEC) ;
keyval_insert("$extern", DLREXTERN) ;
keyval_insert("$extval", DLREXTVAL) ;
keyval_insert("$extype", DLREXTYPE) ;
keyval_insert("$decrypt", DLRDECRYPT) ;
keyval_insert("$delay", DLRDELAY) ;
keyval_insert("$delay_vt", DLRDELAY_VT) ;
keyval_insert("$dynload", DLRDYNLOAD) ;
keyval_insert("$encrypt", DLRENCRYPT) ;
keyval_insert("$fold", DLRFOLD) ;
keyval_insert("$lst", DLRLST_T) ;
keyval_insert("$lst_t", DLRLST_T) ;
keyval_insert("$lst_vt", DLRLST_VT) ;
keyval_insert("$obj", DLROBJ_T) ;
keyval_insert("$obj_t", DLROBJ_T) ;
keyval_insert("$obj_vt", DLROBJ_VT) ;
keyval_insert("$raise", DLRRAISE) ;
keyval_insert("$rec_t", DLRREC_T) ;
keyval_insert("$rec_vt", DLRREC_VT) ;
keyval_insert("$spawn", DLRSPAWN) ;
keyval_insert("$tup_t", DLRTUP_T) ;
keyval_insert("$tup_vt", DLRTUP_VT) ;
keyval_insert("$unfold", DLRUNFOLD) ;
keyval_insert("$typeof", DLRTYPEOF) ;

keyval_insert("fold@", FOLDAT) ;
keyval_insert("free@", FREEAT) ;
keyval_insert("view@", VIEWAT) ;

keyval_insert("r@ead", R0EAD) ;

keyval_insert("t@ype", T0YPE) ;
keyval_insert("t@ype+", T0YPEPLUS) ;
keyval_insert("t@ype-", T0YPEMINUS) ;
keyval_insert("viewt@ype", VIEWT0YPE) ;
keyval_insert("viewt@ype+", VIEWT0YPEPLUS) ;
keyval_insert("viewt@ype-", VIEWT0YPEMINUS) ;
keyval_insert("abst@ype", ABST0YPE) ;
keyval_insert("absviewt@ype", ABSVIEWT0YPE) ;

}

%}

extern fun keyval_table_init (): void = "keyval_table_init"

(* ****** ****** *)

val () = keyval_table_init () // initializing the keyword table

(* ****** ****** *)

(* end of [ats_keyword.dats] *)
