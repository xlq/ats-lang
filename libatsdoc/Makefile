#######################################################################
#                                                                     #
#                         Applied Type System                         #
#                                                                     #
#                              Hongwei Xi                             #
#                                                                     #
#######################################################################

#
# ATS/Postiats - Unleashing the Potential of Types!
# Copyright (C) 2011-20?? Hongwei Xi, ATS Trustworthy Software
# All rights reserved
#
# ATS is  free software;  you can redistribute it and/or modify it under
# the  terms of the  GNU General Public License as published by the Free
# Software Foundation; either version 2.1, or (at your option) any later
# version.
# 
# ATS is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
# for more details.
# 
# You  should  have  received  a  copy of the GNU General Public License
# along  with  ATS;  see the  file COPYING.  If not, please write to the
# Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.
#

######
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Start Time: August, 2011
#
######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

ATSGCFLAG=
ATSGCFLAG=-D_ATS_GCATS

ATSCCFLAGS=-g
ATSCCFLAGS=-g -O
ATSCCFLAGS=-g -O2

######

all:: libatsdoc

######

SOURCES := \
  atsdoc_error.sats \
  atsdoc_error.dats \
  atsdoc_symbol.sats \
  atsdoc_symbol.dats \
  atsdoc_symmap.sats \
  atsdoc_symmap.dats \
  atsdoc_filename.sats \
  atsdoc_filename.dats \
  atsdoc_location.sats \
  atsdoc_location.dats \
  atsdoc_reader.sats \
  atsdoc_reader.dats \
  atsdoc_lexbuf.sats \
  atsdoc_lexbuf.dats \
  atsdoc_text.sats \
  atsdoc_text.dats \

SOURCESsta := $(filter %.sats, $(SOURCES))
SOURCESdyn := $(filter %.dats, $(SOURCES))

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))

######

atsdoc_error_sats.o : SATS/atsdoc_error.sats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_error_dats.o : DATS/atsdoc_error.dats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_symbol_sats.o : SATS/atsdoc_symbol.sats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_symbol_dats.o : DATS/atsdoc_symbol.dats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_symmap_sats.o : SATS/atsdoc_symmap.sats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_symmap_dats.o : DATS/atsdoc_symmap.dats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_filename_sats.o : SATS/atsdoc_filename.sats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_filename_dats.o : DATS/atsdoc_filename.dats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_location_sats.o : SATS/atsdoc_location.sats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_location_dats.o : DATS/atsdoc_location.dats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_reader_sats.o : SATS/atsdoc_reader.sats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_reader_dats.o : DATS/atsdoc_reader.dats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_lexbuf_sats.o : SATS/atsdoc_lexbuf.sats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_lexbuf_dats.o : DATS/atsdoc_lexbuf.dats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_text_sats.o : SATS/atsdoc_text.sats; $(ATSCC) $(ATSCCFLAGS) -c $<
atsdoc_text_dats.o : DATS/atsdoc_text.dats; $(ATSCC) $(ATSCCFLAGS) -c $<

######

libatsdoc: dynloadall.dats $(OBJECTS)
	$(ATSCC) $(ATSCCFLAGS) -c dynloadall.dats
	$(ARR) libatsdoc.a dynloadall_dats.o $(OBJECTS)

######
#
# %_sats.o: %.sats
#	$(ATSCC) $(ATSCCFLAGS) -c $<
#
# %_dats.o: %.dats
#	$(ATSCC) $(ATSCCFLAGS) -c $<
#
######

ARR=ar -r
CPF=cp -f
RMF=rm -f
WCL=wc -l

######

srclines:: ; $(WCL) $(SOURCES)

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.o
clean:: ; $(RMF) *_?ats.c

cleanall:: clean
cleanall:: ; $(RMF) libatsdoc.a

###### end of [Makefile] ######
