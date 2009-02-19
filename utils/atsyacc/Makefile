#########################################################################
#                                                                       #
#                         Applied Type System                           #
#                                                                       #
#                              Hongwei Xi                               #
#                                                                       #
#########################################################################

#
#  ATS - Unleashing the Power of Types!
#
#  Copyright (C) 2002-2009 Hongwei Xi.
#
#  ATS is free software;  you can  redistribute it and/or modify it under
#  the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
#  Free Software Foundation; either version 2.1, or (at your option)  any
#  later version.
# 
#  ATS is distributed in the hope that it will be useful, but WITHOUT ANY
#  WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
#  FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
#  for more details.
# 
#  You  should  have  received  a  copy of the GNU General Public License
#  along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
#  Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
#  02110-1301, USA.
#

#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#

######

LIB=LIB

ATSCC="$(ATSHOME)"/bin/atscc
ATSLEX="$(ATSHOME)"/bin/atslex

GCFLAG=
GCFLAG=-D_ATS_GCATS

CCFLAGS=
CCFLAGS=-O2

######

atsyacc:: \
  atsyacc_main.dats \
  linqueuelst_dats.o \
  funmap_avltree_dats.o \
  funset_avltree_dats.o \
  hashtable_dats.o \
  location_sats.o location_dats.o \
  token_sats.o token_dats.o \
  symbol_sats.o symbol_dats.o \
  atsyacc_top_sats.o \
  atsyacc_lexer_lats.dats \
  atsyacc_parser_dats.o \
  grammar_sats.o grammar_dats.o \
  atsyacc_nullfrstfllw_dats.o \
  atsyacc_lrtable_dats.o \

	$(ATSCC) $(GCFLAG) $(CCFLAGS) -g -o atsyacc \
  atsyacc_main.dats \
  linqueuelst_dats.o \
  funmap_avltree_dats.o \
  funset_avltree_dats.o \
  hashtable_dats.o \
  location_sats.o location_dats.o \
  token_sats.o token_dats.o \
  symbol_sats.o symbol_dats.o \
  atsyacc_top_sats.o \
  atsyacc_lexer_lats.dats -latslex \
  atsyacc_parser_dats.o \
  grammar_sats.o grammar_dats.o \
  atsyacc_nullfrstfllw_dats.o \
  atsyacc_lrtable_dats.o \

######

linqueuelst_dats.o: $(LIB)/linqueuelst.dats
	$(ATSCC) $(CCFLAGS) -c -o linqueuelst_dats.o $(LIB)/linqueuelst.dats

funmap_avltree_dats.o: $(LIB)/funmap_avltree.dats
	$(ATSCC) $(CCFLAGS) -c -o funmap_avltree_dats.o $(LIB)/funmap_avltree.dats

funset_avltree_dats.o: $(LIB)/funset_avltree.dats
	$(ATSCC) $(CCFLAGS) -c -o funset_avltree_dats.o $(LIB)/funset_avltree.dats

hashtable_dats.o: $(LIB)/hashtable.dats
	$(ATSCC) $(CCFLAGS) -c -o hashtable_dats.o $(LIB)/hashtable.dats

######

symbol_sats.o: symbol.sats
	$(ATSCC) $(CCFLAGS) -c -o symbol_sats.o symbol.sats

symbol_dats.o: symbol.dats
	$(ATSCC) $(CCFLAGS) -c -o symbol_dats.o symbol.dats

location_sats.o: location.sats
	$(ATSCC) $(CCFLAGS) -c -o location_sats.o location.sats

location_dats.o: location.dats
	$(ATSCC) $(CCFLAGS) -c -o location_dats.o location.dats

######

token_sats.o: token.sats
	$(ATSCC) $(CCFLAGS) -c -o token_sats.o token.sats

token_dats.o: token.dats
	$(ATSCC) $(CCFLAGS) -c -o token_dats.o token.dats

######

grammar_sats.o: grammar.sats
	$(ATSCC) $(CCFLAGS) -c -o grammar_sats.o grammar.sats

grammar_dats.o: grammar.dats
	$(ATSCC) $(CCFLAGS) -c -o grammar_dats.o grammar.dats

######

atsyacc_nullfrstfllw_dats.o: atsyacc_nullfrstfllw.dats
	$(ATSCC) $(CCFLAGS) -c -o atsyacc_nullfrstfllw_dats.o atsyacc_nullfrstfllw.dats

atsyacc_lrtable_dats.o: atsyacc_lrtable.dats
	$(ATSCC) $(CCFLAGS) -c -o atsyacc_lrtable_dats.o atsyacc_lrtable.dats

######

atsyacc_top_sats.o: atsyacc_top.sats
	$(ATSCC) $(CCFLAGS) -c -o atsyacc_top_sats.o atsyacc_top.sats

atsyacc_lexer_lats.dats: atsyacc_lexer.lats
	$(ATSLEX) < atsyacc_lexer.lats > atsyacc_lexer_lats.dats

atsyacc_parser_dats.o: atsyacc_parser.dats
	$(ATSCC) $(CCFLAGS) -c -o atsyacc_parser_dats.o atsyacc_parser.dats

######

clean::
	rm -f *~
	rm -f *_sats.c *_dats.c *.o
	rm -f atsyacc_lexer_lats.dats

cleanall: clean; rm -f atsyacc

###### end of [Makefile] ######
