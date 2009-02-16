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

ATSCC="$(ATSHOME)"/bin/atscc
ATSLEX="$(ATSHOME)"/bin/atslex

######

atsyacc:: \
  atsyacc_main.dats \
  hashtable_dats.o \
  symbol_sats.o symbol_dats.o \
  location_sats.o location_dats.o \
  atsyacc_token_sats.o atsyacc_token_dats.o \
  atsyacc_top_sats.o \
  atsyacc_lexer_lats.dats \
  atsyacc_parser_dats.o \

	$(ATSCC) -g -o atsyacc \
  atsyacc_main.dats \
  hashtable_dats.o \
  symbol_sats.o symbol_dats.o \
  location_sats.o location_dats.o \
  atsyacc_token_sats.o atsyacc_token_dats.o \
  atsyacc_top_sats.o \
  atsyacc_lexer_lats.dats -latslex \
  atsyacc_parser_dats.o

######

hashtable_dats.o: hashtable.dats
	$(ATSCC) -c -o hashtable_dats.o hashtable.dats

symbol_sats.o: symbol.sats
	$(ATSCC) -c -o symbol_sats.o symbol.sats

symbol_dats.o: symbol.dats
	$(ATSCC) -c -o symbol_dats.o symbol.dats

location_sats.o: location.sats
	$(ATSCC) -c -o location_sats.o location.sats

location_dats.o: location.dats
	$(ATSCC) -c -o location_dats.o location.dats

######

atsyacc_token_sats.o: atsyacc_token.sats
	$(ATSCC) -c -o atsyacc_token_sats.o atsyacc_token.sats

atsyacc_token_dats.o: atsyacc_token.dats
	$(ATSCC) -c -o atsyacc_token_dats.o atsyacc_token.dats

######

atsyacc_top_sats.o: atsyacc_top.sats
	$(ATSCC) -c -o atsyacc_top_sats.o atsyacc_top.sats

atsyacc_lexer_lats.dats: atsyacc_lexer.lats
	$(ATSLEX) < atsyacc_lexer.lats > atsyacc_lexer_lats.dats

atsyacc_parser_dats.o: atsyacc_parser.dats
	$(ATSCC) -c -o atsyacc_parser_dats.o atsyacc_parser.dats

######

clean::
	rm -f *~
	rm -f *_sats.c *_dats.c *.o
	rm -f atsyacc_lexer_lats.dats

cleanall: clean; rm -f atsyacc

###### end of [Makefile] ######
