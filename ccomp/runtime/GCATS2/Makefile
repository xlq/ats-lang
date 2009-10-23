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

## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Time: October 2009

## ###### ###### ##

GCC=gcc
GCCFLAGS= -O2
ATSCC=$(ATSHOME)/bin/atscc
ATSCCFLAGS= -g -O2 # -D_ATS_MULTITHREAD # -m64
#ATSCCFLAGS= -m64

######

gc.o: \
  gcats2_c.h \
  gcats2_ats.hats \
  gcats2_top_dats.c \
  gcats2_misc_dats.c \
  gcats2_freeitmlst_dats.c \
  gcats2_chunk_dats.c \
  gcats2_pointer_dats.c \
  gcats2_globalrts_dats.c \
  gcats2_marking_dats.c \
  gcats2_collecting_dats.c \
  gcats2_autmem_dats.c \
  gcats2_manmem_dats.c
	$(ATSCC) -O2 -c -o gc.o -x c gcats2_all.cats

######

gcats2_c.h: gcats2_master.hats
	$(GCC) -E -P -D_CHEADER -o $@ -x c gcats2_master.hats

gcats2_ats.hats: gcats2_master.hats
	$(GCC) -E -P -D_ATSHEADER -o $@ -x c gcats2_master.hats

######

gcats2_top_dats.c: \
  gcats2_top.dats; $(ATSCC) -cc gcats2_top.dats
gcats2_misc_dats.c: \
  gcats2_misc.dats; $(ATSCC) -cc gcats2_misc.dats 
gcats2_freeitmlst_dats.c: \
  gcats2_freeitmlst.dats; $(ATSCC) -cc gcats2_freeitmlst.dats 
gcats2_chunk_dats.c: \
  gcats2_chunk.dats; $(ATSCC) -cc gcats2_chunk.dats 
gcats2_pointer_dats.c: \
  gcats2_pointer.dats; $(ATSCC) -cc gcats2_pointer.dats 
gcats2_globalrts_dats.c: \
  gcats2_globalrts.dats; $(ATSCC) -cc gcats2_globalrts.dats 
gcats2_marking_dats.c: \
  gcats2_marking.dats; $(ATSCC) -cc gcats2_marking.dats 
gcats2_collecting_dats.c: \
  gcats2_collecting.dats; $(ATSCC) -cc gcats2_collecting.dats 
gcats2_autmem_dats.c: \
  gcats2_autmem.dats; $(ATSCC) -cc gcats2_autmem.dats 
gcats2_manmem_dats.c: \
  gcats2_manmem.dats; $(ATSCC) -cc gcats2_manmem.dats 

######

test: gcats2_c.h gcats2_ats.hats
	$(ATSCC) $(ATSCCFLAGS) -o test gcats2_test.dats \
          gcats2.sats \
          gcats2_top.dats \
          gcats2_misc.dats \
          gcats2_freeitmlst.dats \
          gcats2_chunk.dats \
          gcats2_pointer.dats \
          gcats2_globalrts.dats \
          gcats2_marking.dats \
          gcats2_collecting.dats \
          gcats2_autmem.dats \
          gcats2_manmem.dats \
          -lpthread \
      && ./test \
      && rm -f ./test

######

clean::
	rm -f gcats2_c.h
	rm -f gcats2_ats.hats
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f *.o test

###### end of [Makefile] ######
