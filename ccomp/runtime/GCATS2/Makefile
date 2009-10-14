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
ATSCC=$(ATSHOME)/bin/atscc -O3
ATSCCFLAGS= # -m64

######

test: gcats2_c.h gcats2_ats.hats
	$(ATSCC) $(ATSCCFLAGS) -o test gcats2_test.dats \
          gcats2.sats \
          gcats2_top.dats \
          gcats2_freeitmlst.dats \
          gcats2_chunk.dats \
          gcats2_pointer.dats \
          gcats2_marking.dats \
      && ./test

######

gcats2_c.h: gcats2_master.hats
	$(GCC) -E -P -D_CHEADER -o $@ -x c gcats2_master.hats

gcats2_ats.hats: gcats2_master.hats
	$(GCC) -E -P -D_ATSHEADER -o $@ -x c gcats2_master.hats

######

gcats2_freeitmlst_dats.o: \
  gcats2_c.h gcats2_ats.hats gcats2_freeitmlst.dats 
	$(ATSCC) $(ATSCCFLAGS) -o $@  -c gcats2_freeitmlst.dats

gcats2_chunk_dats.o: \
  gcats2_c.h gcats2_ats.hats gcats2_chunk.dats 
	$(ATSCC) $(ATSCCFLAGS) -o $@  -c gcats2_chunk.dats

gcats2_pointer_dats.o: \
  gcats2_c.h gcats2_ats.hats gcats2_pointer.dats 
	$(ATSCC) $(ATSCCFLAGS) -o $@ -c gcats2_pointer.dats

gcats2_marking_dats.o: \
  gcats2_c.h gcats2_ats.hats gcats2_marking.dats 
	$(ATSCC) $(ATSCCFLAGS) -o $@  -c gcats2_marking.dats

######

clean::
	rm -f gcats2_c.h
	rm -f gcats2_ats.hats
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f *.o test

###### end of [Makefile] ######
