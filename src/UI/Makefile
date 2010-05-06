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
## Copyright (C) 2010-201? Hongwei Xi, Boston University
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
## Time: April 2010

######

MAKE=make
ATSCC="$(ATSHOME)"/bin/atscc
ATSCCFLAGS=-g

GTKLIBS=`pkg-config gtk+-2.0 --libs`
GTKCCFLAGS=`pkg-config gtk+-2.0 --cflags`

######

SOURCES := \
  atsui_util.sats atsui_util.dats \
  atsui_comp.sats atsui_comp.dats \
  atsui_srcwinlst.sats atsui_srcwinlst.dats \
  atsui_topenv.sats atsui_topenv.dats \

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))

######

atsui: \
  atsui_main_dats.o \
  $(OBJECTS)
	$(ATSCC) \
  $(ATSCCFLAGS) \
  $(GTKCCFLAGS) \
  -o atsui \
  atsui_main_dats.o \
  $(OBJECTS) \
  $(GTKLIBS) \

######

atsui_main_dats.o: atsui_main.dats
	$(ATSCC) $(ATSCCFLAGS) $(GTKCCFLAGS) -c atsui_main.dats

######

atsui_util_sats.o: atsui_util.sats
	$(ATSCC) $(ATSCCFLAGS) $(GTKCCFLAGS) -c atsui_util.sats

atsui_util_dats.o: atsui_util.dats
	$(ATSCC) $(ATSCCFLAGS) $(GTKCCFLAGS) -c atsui_util.dats

######

atsui_comp_sats.o: atsui_comp.sats
	$(ATSCC) $(ATSCCFLAGS) $(GTKCCFLAGS) -c atsui_comp.sats

atsui_comp_dats.o: atsui_comp.dats
	$(ATSCC) $(ATSCCFLAGS) $(GTKCCFLAGS) -c atsui_comp.dats

######

atsui_srcwinlst_sats.o: atsui_srcwinlst.sats
	$(ATSCC) $(ATSCCFLAGS) $(GTKCCFLAGS) -c atsui_srcwinlst.sats

atsui_srcwinlst_dats.o: atsui_srcwinlst.dats
	$(ATSCC) $(ATSCCFLAGS) $(GTKCCFLAGS) -c atsui_srcwinlst.dats

######

atsui_topenv_sats.o: atsui_topenv.sats
	$(ATSCC) $(ATSCCFLAGS) $(GTKCCFLAGS) -c atsui_topenv.sats

atsui_topenv_dats.o: atsui_topenv.dats
	$(ATSCC) $(ATSCCFLAGS) $(GTKCCFLAGS) -c atsui_topenv.dats

######

clean::
	rm -f *~
	rm -f *_?ats.c  *_?ats.o

cleanall: clean
	rm -f atsui

######

## end of [Makefile] ##

######
