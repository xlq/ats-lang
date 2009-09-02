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
## Time: June 2008

## ###### ###### ##

GCC=gcc
ATSCC="${ATSHOME}"/bin/atscc

#ATSCCFLAG=-g
#ATSCCFLAG=-DGCATS_DEBUG
#ATSCCFLAG=-g
ATSCCFLAG=-O3 -g
#ATSCCFLAG=-O3
#CCFLAG=
CCFLAG=-O3

SOURCES := \
  gc_misc.dats \
  gc_freeitmlst.dats \
  gc_chunk.dats \
  gc_globalentry.dats \
  gc_marking.dats \
  gc_collecting.dats \
  gc_autops.dats \
  gc_manops.dats \
  gc_top.dats \

TARGETS := $(patsubst %.dats, %_dats.c, $(SOURCES))
TARGETS_mt := $(TARGETS) gc_multithread_dats.c
OBJECTS := $(patsubst %.dats, %_dats.o, $(SOURCES))
OBJECTS_mt := $(OBJECTS) gc_multithread_dats.o

######

#
# this generates a slower version:
#
# gc.o: gc_sats.o $(OBJECTS)
#	ld -r -o gc.o gc_sats.o $(OBJECTS)
#

gc.o: gc0_hats gc_sats.o gc_all_cats.o
	ld -r -o gc.o gc_sats.o gc_all_cats.o

gc_mt.o: gc1_hats gc_sats.o gc_mt_all_cats.o
	ld -r -o gc_mt.o gc_sats.o gc_mt_all_cats.o

######

#
# mainly for the purpose of debugging
#
gc_main: gc0_hats gc.cats gc_sats.c gc_main.dats $(OBJECTS)
	$(ATSCC) $(CCFLAG) -o gc_main gc_main.dats gc_sats.c $(OBJECTS)

gc_main_mt: gc1_hats gc.cats gc_sats.c gc_main.dats $(OBJECTS_mt)
	$(ATSCC) $(CCFLAG) -pthread -o gc_main_mt gc_main.dats gc_sats.c $(OBJECTS_mt)

######

gc0_hats: ; gcc -E -P -D_ATS_MULTITHREAD0 -x c gc_master.hats -o gc.hats
gc1_hats: ; gcc -E -P -D_ATS_MULTITHREAD1 -x c gc_master.hats -o gc.hats

######

#
# this kind of whole compilation can probably take advantage of
# interprocedural optimization:
#
gc_all_cats.o: gc_sats.c $(TARGETS)
	$(ATSCC) $(CCFLAG) -o gc_all_cats.o -c -x c gc_all.cats

gc_mt_all_cats.o: gc_sats.c $(TARGETS_mt)
	$(ATSCC) $(CCFLAG) -o gc_mt_all_cats.o -c -x c gc_all.cats

######

gc_sats.c: gc.sats
	$(ATSCC) $(ATSCCFLAG) -cc gc.sats
gc_sats.o: gc_sats.c; $(ATSCC) $(CCFLAG) -c gc_sats.c

######

gc_top_dats.c: gc_top.dats
	$(ATSCC) $(ATSCCFLAG) -cc gc_top.dats
gc_top_dats.o: gc_top_dats.c; $(ATSCC) $(CCFLAG) -c gc_top_dats.c

gc_misc_dats.c: gc_misc.dats
	$(ATSCC) $(ATSCCFLAG) -cc gc_misc.dats
gc_misc_dats.o: gc_misc_dats.c
	$(ATSCC) $(CCFLAG) -c gc_misc_dats.c

gc_freeitmlst_dats.c: gc_freeitmlst.dats
	$(ATSCC) $(ATSCCFLAG) -cc gc_freeitmlst.dats
gc_freeitmlst_dats.o: gc_freeitmlst_dats.c
	$(ATSCC) $(CCFLAG) -c gc_freeitmlst_dats.c

gc_chunk_dats.c: gc_chunk.dats
	$(ATSCC) $(ATSCCFLAG) -cc gc_chunk.dats
gc_chunk_dats.o: gc_chunk_dats.c
	$(ATSCC) $(CCFLAG) -c gc_chunk_dats.c

gc_globalentry_dats.c: gc_globalentry.dats
	$(ATSCC) $(ATSCCFLAG) -cc gc_globalentry.dats
gc_globalentry_dats.o: gc_globalentry_dats.c
	$(ATSCC) $(CCFLAG) -c gc_globalentry_dats.c

gc_multithread_dats.c: gc_multithread.dats
	$(ATSCC) $(ATSCCFLAG) -cc gc_multithread.dats
gc_multithread_dats.o: gc_multithread_dats.c
	$(ATSCC) $(CCFLAG) -c gc_multithread_dats.c

gc_marking_dats.c: gc_marking.dats
	$(ATSCC) $(ATSCCFLAG) -cc gc_marking.dats
gc_marking_dats.o: gc_marking_dats.c
	$(ATSCC) $(CCFLAG) -c gc_marking_dats.c

gc_collecting_dats.c: gc_collecting.dats
	$(ATSCC) $(ATSCCFLAG) -cc gc_collecting.dats
gc_collecting_dats.o: gc_collecting_dats.c
	$(ATSCC) $(CCFLAG) -c gc_collecting_dats.c

gc_autops_dats.c: gc_autops.dats
	$(ATSCC) $(ATSCCFLAG) -cc gc_autops.dats
gc_autops_dats.o: gc_autops_dats.c
	$(ATSCC) $(CCFLAG) -c gc_autops_dats.c

gc_manops_dats.c: gc_manops.dats
	$(ATSCC) $(ATSCCFLAG) -cc gc_manops.dats
gc_manops_dats.o: gc_manops_dats.c
	$(ATSCC) $(CCFLAG) -c gc_manops_dats.c

######

lines::
	wc -l *.?ats

######

clean::
	rm -f gc.hats *_?ats.c *_?ats.o *~

cleanall:: clean; rm -f gc.o gc_mt.o gc_main gc_main_mt

######
#
# end of [Makefile]
#
######
