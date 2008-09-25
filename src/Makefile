#########################################################################
##                                                                     ##
##                         Applied Type System                         ##
##                                                                     ##
##                              Hongwei Xi                             ##
##                                                                     ##
#########################################################################

##
## ATS/Anairiats - Unleashing the Power of Types!
##
## Copyright (C) 2002-2008 Hongwei Xi, Boston University
##
## All rights reserved
##
## ATS is  free software;  you can redistribute it and/or modify it under
## the  terms of the  GNU General Public License as published by the Free
## Software Foundation; either version 2.1, or (at your option) any later
## version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

## ###### ###### ##

## Time: July 2007
## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

## ###### ###### ##


DIR=.
CC=gcc
YACC=yacc
#YACC=byacc

ATSCC="$(ATSHOME)"/bin/atscc

#ATSCCFLAG=-g
#ATSCCFLAG=-O0
#ATSCCFLAG=-O1
#ATSCCFLAG=-O2
ATSCCFLAG=-D_ATS_MULTITHREAD -O2 -g

#GCFLAG=-D_ATS_gc
#GCFLAG=-D_ATS_gcats
#GCFLAG=-D_ATS_GC
GCFLAG=-D_ATS_GCATS -pthread
GC_o=gc_mt_o

ATSLEX="$(ATSHOME)"/bin/atslex

######

SOURCES := \
  ats_array.sats ats_array.dats \
  ats_charlst.sats ats_charlst.dats \
  ats_comarg.sats ats_comarg.dats \
  ats_counter.sats ats_counter.dats \
  ats_debug.sats ats_debug.dats \
  ats_effect.sats ats_effect.dats \
  ats_error.sats ats_error.dats \
  ats_filename.sats ats_filename.dats \
  ats_fixity.sats ats_fixity.dats \
  ats_global.sats ats_global.dats \
  ats_hashtbl.sats ats_hashtbl.dats \
  ats_intinf.sats ats_intinf.dats \
  ats_keyword.sats ats_keyword.dats \
  ats_label.sats ats_label.dats \
  ats_location.sats ats_location.dats \
  ats_namespace.sats ats_namespace.dats \
  ats_posmark.sats ats_posmark.dats \
  ats_stamp.sats ats_stamp.dats \
  ats_symbol.sats ats_symbol.dats \
  ats_symenv.sats ats_symenv.dats \
  ats_symtbl.sats ats_symtbl.dats \
  ats_list.sats ats_list.dats \
  ats_map_lin.sats ats_map_lin.dats \
  ats_reference.sats ats_reference.dats \
  ats_set_fun.sats ats_set_fun.dats \
  ats_parser.sats ats_parser.dats \
  ats_syntax.sats ats_syntax.dats ats_syntax_posmark.dats \
  ats_staexp1.sats ats_staexp1.dats ats_staexp1_print.dats \
  ats_dynexp1.sats ats_dynexp1.dats ats_dynexp1_print.dats \
  ats_trans1_env.sats ats_trans1_env.dats \
  ats_e1xp_eval.sats ats_e1xp_eval.dats \
  ats_trans1.sats ats_trans1_sta.dats ats_trans1_dyn.dats \
  ats_staexp2.sats ats_staexp2.dats \
  ats_staexp2_scst.dats \
  ats_staexp2_svVar.dats \
  ats_staexp2_dcon.dats \
  ats_staexp2_print.dats \
  ats_staexp2_util1.dats ats_staexp2_util2.dats \
  ats_dynexp2.sats \
  ats_dynexp2.dats \
  ats_dynexp2_dcst.dats \
  ats_dynexp2_dmac.dats \
  ats_dynexp2_dvar.dats \
  ats_dynexp2_print.dats \
  ats_dynexp2_util.dats \
  ats_trans2_env.sats ats_trans2_env.dats \
  ats_stadyncst2.sats ats_stadyncst2.dats \
  ats_trans2.sats \
  ats_trans2_sta.dats ats_trans2_dyn.dats \
  ats_macro2.sats ats_macro2.dats \
  ats_patcst2.sats ats_patcst2.dats \
  ats_string_parse.sats ats_string_parse.dats \
  ats_printf_c.lats \
  ats_dynexp3.sats ats_dynexp3.dats \
  ats_dynexp3_print.dats \
  ats_trans3_env.sats \
  ats_trans3_env.dats \
  ats_trans3_env_eff.dats \
  ats_trans3_env_loop.dats \
  ats_trans3_env_met.dats \
  ats_trans3_env_scst.dats \
  ats_trans3_env_state.dats \
  ats_trans3_env_print.dats \
  ats_staexp2_solve.sats ats_staexp2_solve.dats \
  ats_trans3.sats ats_trans3_pat.dats \
  ats_trans3_assgn.dats \
  ats_trans3_deref.dats \
  ats_trans3_view.dats \
  ats_trans3_exp_up.dats \
  ats_trans3_exp_dn.dats \
  ats_trans3_loop.dats ats_trans3_dec.dats \
  ats_constraint.sats ats_constraint.dats \
  ats_constraint_print.dats \
  ats_solver_fm.sats ats_solver_fm.dats \
  ats_hiexp.sats ats_hiexp.dats \
  ats_hiexp_print.dats ats_hiexp_util.dats \
  ats_trans4.sats ats_trans4.dats \
  ats_ccomp.sats ats_ccomp.dats \
  ats_ccomp_env.sats ats_ccomp_env.dats \
  ats_ccomp_print.dats \
  ats_ccomp_util.dats \
  ats_ccomp_trans.dats \
  ats_ccomp_trans_clau.dats \
  ats_ccomp_trans_tailcal.dats \
  ats_ccomp_trans_temp.dats \
  ats_ccomp_emit.dats \
  ats_ccomp_main.dats \


SOURCESsta := $(filter %.sats, $(SOURCES))
SOURCESdyn := $(filter %.dats, $(SOURCES))

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))
OBJECTS := $(patsubst %.lats, %_lats_dats.o, $(OBJECTS))

######

LIBOBJS := -lgmp

######

atsopt: $(GC_o) \
  ats_main_dats.o \
  ats_lexer_lats_dats.o ats_lexer_sats.o \
  ats_grammar_yats.o \
  libc_sats.o libats_lex.o \
  $(OBJECTS)
	$(ATSCC) $(GCFLAG) $(ATSCCFLAG) \
  -o atsopt \
  ats_main_dats.o \
  ats_lexer_lats_dats.o ats_lexer_sats.o \
  ats_grammar_yats.o \
  libc_sats.o libats_lex.o \
  $(OBJECTS) \
  $(LIBOBJS)

######

ats_main_dats.o: ats_main.dats \
   ats_lexer_lats.dats ats_printf_c_lats.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_main.dats

######

ats_lexer_lats.dats: ats_lexer.lats
	$(ATSLEX) < ats_lexer.lats > ats_lexer_lats.dats

ats_lexer_sats.o: ats_lexer.sats; $(ATSCC) $(ATSCCFLAG) -c ats_lexer.sats
ats_lexer_lats_dats.o: ats_grammar_yats.h ats_lexer_lats.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_lexer_lats.dats

######

ats_grammar_yats.c ats_grammar_yats.h: ats_grammar.yats
	$(YACC) -v -d -o ats_grammar_yats.c ats_grammar.yats

ats_grammar_yats.o: ats_grammar_yats.c
	$(ATSCC) $(ATSCCFLAG) -DYYDEBUG -c ats_grammar_yats.c 

######

libc_sats_gmp_sats.o: libc_sats_gmp.sats
	$(ATSCC) $(ATSCCFLAG) -c libc_sats_gmp.sats

libc_sats_time_sats.o: libc_sats_time.sats
	$(ATSCC) $(ATSCCFLAG) -c libc_sats_time.sats

libc_sats.o: \
  libc_sats_gmp_sats.o libc_sats_time_sats.o
	ld -r -o $@ \
  libc_sats_gmp_sats.o libc_sats_time_sats.o

######

libats_lex_lexing_sats.o: libats_lex_lexing.sats
	$(ATSCC) $(ATSCCFLAG) -c libats_lex_lexing.sats

libats_lex_lexing_dats.o: libats_lex_lexing.dats
	$(ATSCC) $(ATSCCFLAG) -c libats_lex_lexing.dats

libats_lex_tables_dats.o: libats_lex_tables.dats
	$(ATSCC) $(ATSCCFLAG) -c libats_lex_tables.dats

libats_lex.o: \
  libats_lex_lexing_sats.o libats_lex_lexing_dats.o libats_lex_tables_dats.o
	ld -r -o $@ \
  libats_lex_lexing_sats.o libats_lex_lexing_dats.o libats_lex_tables_dats.o

######

ats_array_sats.o: ats_array.sats; $(ATSCC) $(ATSCCFLAG) -c ats_array.sats
ats_array_dats.o: ats_array.dats; $(ATSCC) $(ATSCCFLAG) -c ats_array.dats

ats_charlst_sats.o: ats_charlst.sats; $(ATSCC) $(ATSCCFLAG) -c ats_charlst.sats
ats_charlst_dats.o: ats_charlst.dats; $(ATSCC) $(ATSCCFLAG) -c ats_charlst.dats

ats_comarg_sats.o: ats_comarg.sats; $(ATSCC) $(ATSCCFLAG) -c ats_comarg.sats
ats_comarg_dats.o: ats_comarg.dats; $(ATSCC) $(ATSCCFLAG) -c ats_comarg.dats

ats_counter_sats.o: ats_counter.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_counter.sats
ats_counter_dats.o: ats_counter.dats ats_counter.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_counter.dats

ats_debug_sats.o: ats_debug.sats; $(ATSCC) $(ATSCCFLAG) -c ats_debug.sats
ats_debug_dats.o: ats_debug.dats; $(ATSCC) $(ATSCCFLAG) -c ats_debug.dats

ats_effect_sats.o: ats_effect.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_effect.sats
ats_effect_dats.o: ats_effect.dats ats_effect.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_effect.dats

ats_error_sats.o: ats_error.sats; $(ATSCC) $(ATSCCFLAG) -c ats_error.sats
ats_error_dats.o: ats_error.dats; $(ATSCC) $(ATSCCFLAG) -c ats_error.dats

ats_e1xp_eval_sats.o: ats_e1xp_eval.sats; $(ATSCC) $(ATSCCFLAG) -c ats_e1xp_eval.sats
ats_e1xp_eval_dats.o: ats_e1xp_eval.dats; $(ATSCC) $(ATSCCFLAG) -c ats_e1xp_eval.dats

ats_filename_sats.o: ats_filename.sats; $(ATSCC) $(ATSCCFLAG) -c ats_filename.sats
ats_filename_dats.o: ats_filename.dats; $(ATSCC) $(ATSCCFLAG) -c ats_filename.dats

ats_fixity_sats.o: ats_fixity.sats; $(ATSCC) $(ATSCCFLAG) -c ats_fixity.sats
ats_fixity_dats.o: ats_fixity.dats; $(ATSCC) $(ATSCCFLAG) -c ats_fixity.dats

ats_global_sats.o: ats_global.sats; $(ATSCC) $(ATSCCFLAG) -c ats_global.sats
ats_global_dats.o: ats_global.dats; $(ATSCC) $(ATSCCFLAG) -c ats_global.dats

ats_hashtbl_sats.o: ats_hashtbl.sats; $(ATSCC) $(ATSCCFLAG) -c ats_hashtbl.sats
ats_hashtbl_dats.o: ats_hashtbl.dats; $(ATSCC) $(ATSCCFLAG) -c ats_hashtbl.dats

ats_intinf_sats.o: ats_intinf.sats; $(ATSCC) $(ATSCCFLAG) -c ats_intinf.sats
ats_intinf_dats.o: ats_intinf.dats; $(ATSCC) $(ATSCCFLAG) -c ats_intinf.dats

ats_keyword_sats.o: ats_keyword.sats;
	$(ATSCC) $(ATSCCFLAG) -c ats_keyword.sats
ats_keyword_dats.o: ats_keyword.dats ats_keyword.sats ats_grammar_yats.h
	$(ATSCC) $(ATSCCFLAG) -c ats_keyword.dats

ats_label_sats.o: ats_label.sats; $(ATSCC) $(ATSCCFLAG) $(ATSCCFLAG) -c ats_label.sats
ats_label_dats.o: ats_label.dats; $(ATSCC) $(ATSCCFLAG) -c ats_label.dats

ats_location_sats.o: ats_location.sats; $(ATSCC) $(ATSCCFLAG) -c ats_location.sats
ats_location_dats.o: ats_location.dats; $(ATSCC) $(ATSCCFLAG) -c ats_location.dats

ats_namespace_sats.o: ats_namespace.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_namespace.sats
ats_namespace_dats.o: ats_namespace.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_namespace.dats

ats_parser_sats.o: ats_parser.sats; $(ATSCC) $(ATSCCFLAG) -c ats_parser.sats
ats_parser_dats.o: ats_parser.dats; $(ATSCC) $(ATSCCFLAG) -c ats_parser.dats

ats_posmark_sats.o: ats_posmark.sats; $(ATSCC) $(ATSCCFLAG) -c ats_posmark.sats
ats_posmark_dats.o: ats_posmark.dats; $(ATSCC) $(ATSCCFLAG) -c ats_posmark.dats

ats_stamp_sats.o: ats_stamp.sats; $(ATSCC) $(ATSCCFLAG) -c ats_stamp.sats
ats_stamp_dats.o: ats_stamp.dats; $(ATSCC) $(ATSCCFLAG) -c ats_stamp.dats

ats_symbol_sats.o: ats_symbol.sats; $(ATSCC) $(ATSCCFLAG) -c ats_symbol.sats
ats_symbol_dats.o: ats_symbol.dats; $(ATSCC) $(ATSCCFLAG) -c ats_symbol.dats

ats_symtbl_sats.o: ats_symtbl.sats; $(ATSCC) $(ATSCCFLAG) -c ats_symtbl.sats
ats_symtbl_dats.o: ats_symtbl.dats; $(ATSCC) $(ATSCCFLAG) -c ats_symtbl.dats

ats_symenv_sats.o: ats_symenv.sats; $(ATSCC) $(ATSCCFLAG) -c ats_symenv.sats
ats_symenv_dats.o: ats_symenv.dats; $(ATSCC) $(ATSCCFLAG) -c ats_symenv.dats

ats_list_sats.o: ats_list.sats; $(ATSCC) $(ATSCCFLAG) -c ats_list.sats
ats_list_dats.o: ats_list.dats; $(ATSCC) $(ATSCCFLAG) -c ats_list.dats

ats_map_lin_sats.o: ats_map_lin.sats; $(ATSCC) $(ATSCCFLAG) -c ats_map_lin.sats
ats_map_lin_dats.o: ats_map_lin.dats; $(ATSCC) $(ATSCCFLAG) -c ats_map_lin.dats

ats_reference_sats.o: ats_reference.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_reference.sats
ats_reference_dats.o: ats_reference.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_reference.dats

ats_set_fun_sats.o: ats_set_fun.sats; $(ATSCC) $(ATSCCFLAG) -c ats_set_fun.sats
ats_set_fun_dats.o: ats_set_fun.dats; $(ATSCC) $(ATSCCFLAG) -c ats_set_fun.dats

ats_syntax_sats.o: ats_syntax.sats; $(ATSCC) $(ATSCCFLAG) -c ats_syntax.sats
ats_syntax_dats.o: ats_syntax.dats; $(ATSCC) $(ATSCCFLAG) -c ats_syntax.dats
ats_syntax_posmark_dats.o: ats_syntax_posmark.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_syntax_posmark.dats

ats_staexp1_sats.o: ats_staexp1.sats; $(ATSCC) $(ATSCCFLAG) -c ats_staexp1.sats
ats_staexp1_dats.o: ats_staexp1.dats; $(ATSCC) $(ATSCCFLAG) -c ats_staexp1.dats
ats_staexp1_print_dats.o: ats_staexp1_print.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_staexp1_print.dats

ats_dynexp1_sats.o: ats_dynexp1.sats; $(ATSCC) $(ATSCCFLAG) -c ats_dynexp1.sats
ats_dynexp1_dats.o: ats_dynexp1.dats; $(ATSCC) $(ATSCCFLAG) -c ats_dynexp1.dats
ats_dynexp1_print_dats.o: ats_dynexp1_print.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_dynexp1_print.dats

ats_trans1_env_sats.o: ats_trans1_env.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans1_env.sats
ats_trans1_env_dats.o: ats_trans1_env.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans1_env.dats

ats_trans1_sats.o: ats_trans1.sats; $(ATSCC) $(ATSCCFLAG) -c ats_trans1.sats
ats_trans1_sta_dats.o: ats_trans1_sta.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans1_sta.dats
ats_trans1_dyn_dats.o: ats_trans1_dyn.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans1_dyn.dats

ats_staexp2_sats.o: ats_staexp2.sats; $(ATSCC) $(ATSCCFLAG) -c ats_staexp2.sats

ats_staexp2_scst_dats.o: ats_staexp2_scst.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_staexp2_scst.dats

ats_staexp2_svVar_dats.o: ats_staexp2_svVar.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_staexp2_svVar.dats

ats_staexp2_dcon_dats.o: ats_staexp2_dcon.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_staexp2_dcon.dats

ats_staexp2_dats.o: ats_staexp2.dats; $(ATSCC) $(ATSCCFLAG) -c ats_staexp2.dats
ats_staexp2_print_dats.o: ats_staexp2_print.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_staexp2_print.dats

ats_staexp2_util1_dats.o: ats_staexp2_util1.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_staexp2_util1.dats
ats_staexp2_util2_dats.o: ats_staexp2_util2.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_staexp2_util2.dats

ats_dynexp2_sats.o: ats_dynexp2.sats; $(ATSCC) $(ATSCCFLAG) -c ats_dynexp2.sats

ats_dynexp2_dcst_dats.o: ats_dynexp2_dcst.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_dynexp2_dcst.dats

ats_dynexp2_dmac_dats.o: ats_dynexp2_dmac.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_dynexp2_dmac.dats

ats_dynexp2_dvar_dats.o: ats_dynexp2_dvar.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_dynexp2_dvar.dats

ats_dynexp2_dats.o: ats_dynexp2.dats; $(ATSCC) $(ATSCCFLAG) -c ats_dynexp2.dats
ats_dynexp2_print_dats.o: ats_dynexp2_print.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_dynexp2_print.dats

ats_dynexp2_util_dats.o: ats_dynexp2_util.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_dynexp2_util.dats

ats_trans2_env_sats.o: ats_trans2_env.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans2_env.sats
ats_trans2_env_dats.o: ats_trans2_env.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans2_env.dats

ats_stadyncst2_sats.o: ats_stadyncst2.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_stadyncst2.sats
ats_stadyncst2_dats.o: ats_stadyncst2.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_stadyncst2.dats

ats_trans2_sats.o: ats_trans2.sats; $(ATSCC) $(ATSCCFLAG) -c ats_trans2.sats
ats_trans2_sta_dats.o: ats_trans2_sta.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans2_sta.dats
ats_trans2_dyn_dats.o: ats_trans2_dyn.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans2_dyn.dats

ats_macro2_sats.o: ats_macro2.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_macro2.sats
ats_macro2_dats.o: ats_macro2.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_macro2.dats

ats_patcst2_sats.o: ats_patcst2.sats; $(ATSCC) $(ATSCCFLAG) -c ats_patcst2.sats
ats_patcst2_dats.o: ats_patcst2.dats; $(ATSCC) $(ATSCCFLAG) -c ats_patcst2.dats

ats_string_parse_sats.o: ats_string_parse.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_string_parse.sats
ats_string_parse_dats.o: ats_string_parse.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_string_parse.dats

ats_printf_c_lats.dats: ats_printf_c.lats
	$(ATSLEX) < ats_printf_c.lats > ats_printf_c_lats.dats
ats_printf_c_lats_dats.o: ats_printf_c_lats.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_printf_c_lats.dats

ats_trans3_env_sats.o: ats_trans3_env.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_env.sats

ats_staexp2_solve_sats.o : ats_staexp2_solve.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_staexp2_solve.sats
ats_staexp2_solve_dats.o : ats_staexp2_solve.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_staexp2_solve.dats

ats_trans3_env_eff_dats.o: ats_trans3_env_eff.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_env_eff.dats

ats_trans3_env_loop_dats.o: ats_trans3_env_loop.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_env_loop.dats

ats_trans3_env_met_dats.o: ats_trans3_env_met.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_env_met.dats

ats_trans3_env_scst_dats.o: ats_trans3_env_scst.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_env_scst.dats

ats_trans3_env_state_dats.o: ats_trans3_env_state.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_env_state.dats

ats_trans3_env_dats.o: ats_trans3_env.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_env.dats
ats_trans3_env_print_dats.o: ats_trans3_env_print.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_env_print.dats

ats_dynexp3_sats.o: ats_dynexp3.sats; $(ATSCC) $(ATSCCFLAG) -c ats_dynexp3.sats

ats_dynexp3_dats.o: ats_dynexp3.dats; $(ATSCC) $(ATSCCFLAG) -c ats_dynexp3.dats
ats_dynexp3_print_dats.o: ats_dynexp3_print.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_dynexp3_print.dats

ats_trans3_sats.o: ats_trans3.sats; $(ATSCC) $(ATSCCFLAG) -c ats_trans3.sats

ats_trans3_pat_dats.o: ats_trans3_pat.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_pat.dats

ats_trans3_assgn_dats.o: ats_trans3_assgn.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_assgn.dats
ats_trans3_deref_dats.o: ats_trans3_deref.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_deref.dats

ats_trans3_view_dats.o: ats_trans3_view.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_view.dats

ats_trans3_exp_up_dats.o: ats_trans3_exp_up.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_exp_up.dats
ats_trans3_exp_dn_dats.o: ats_trans3_exp_dn.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_exp_dn.dats

ats_trans3_loop_dats.o: ats_trans3_loop.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_loop.dats

ats_trans3_dec_dats.o: ats_trans3_dec.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans3_dec.dats

ats_constraint_sats.o: ats_constraint.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_constraint.sats
ats_constraint_dats.o: ats_constraint.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_constraint.dats
ats_constraint_print_dats.o: ats_constraint_print.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_constraint_print.dats

ats_solver_fm_sats.o: ats_solver_fm.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_solver_fm.sats
ats_solver_fm_dats.o: ats_solver_fm.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_solver_fm.dats

ats_hiexp_sats.o: ats_hiexp.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_hiexp.sats
ats_hiexp_dats.o: ats_hiexp.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_hiexp.dats

ats_hiexp_print_dats.o: ats_hiexp_print.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_hiexp_print.dats

ats_hiexp_util_dats.o: ats_hiexp_util.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_hiexp_util.dats

ats_trans4_sats.o: ats_trans4.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans4.sats
ats_trans4_dats.o: ats_trans4.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_trans4.dats

ats_ccomp_sats.o: ats_ccomp.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp.sats
ats_ccomp_dats.o: ats_ccomp.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp.dats

ats_ccomp_print_dats.o: ats_ccomp_print.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp_print.dats

ats_ccomp_env_sats.o: ats_ccomp_env.sats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp_env.sats
ats_ccomp_env_dats.o: ats_ccomp_env.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp_env.dats

ats_ccomp_util_dats.o: ats_ccomp_util.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp_util.dats

ats_ccomp_trans_dats.o: ats_ccomp_trans.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp_trans.dats

ats_ccomp_trans_clau_dats.o: ats_ccomp_trans_clau.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp_trans_clau.dats

ats_ccomp_trans_tailcal_dats.o: ats_ccomp_trans_tailcal.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp_trans_tailcal.dats

ats_ccomp_trans_temp_dats.o: ats_ccomp_trans_temp.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp_trans_temp.dats

ats_ccomp_emit_dats.o: ats_ccomp_emit.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp_emit.dats

ats_ccomp_main_dats.o: ats_ccomp_main.dats
	$(ATSCC) $(ATSCCFLAG) -c ats_ccomp_main.dats

######

gc_o:
	cd "$(ATSHOME)"/ccomp/runtime/GCATS; make gc.o; make clean

gc_mt_o:
	cd "$(ATSHOME)"/ccomp/runtime/GCATS; make gc_mt.o; make clean

######

lines:
	wc -l \
  ats_main.dats \
  ats_lexer.lats \
  ats_grammar.yats \
  libats_lex_lexing.sats \
  libats_lex_lexing.dats \
  libats_lex_tables.dats \
  ats_main.cats \
  ats_counter.cats \
  ats_gmp.cats \
  ats_intinf.cats \
  ats_solver_fm.cats \
  $(SOURCES)

######

clean::
	rm -f $(DIR)/*_?ats.o
	rm -f $(DIR)/*_sats.c
	rm -f $(DIR)/*_dats.c
	rm -f $(DIR)/*_?ats.html
	rm -f $(DIR)/*_lats.dats
	rm -f $(DIR)/ats_grammar_yats.output
	rm -f $(DIR)/*~

######

#depend: ; ./atsopt -dep -s $(SOURCESsta) -d $(SOURCESdyn) >! .depend

include .depend

######

## end of [Makefile] ##

######
