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
#  Copyright (C) 2002-2007 Hongwei Xi.
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

######

#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSCCFLAGS=
ATSRUNTIME=$(ATSHOMEQ)/ccomp/runtime
IATS=-IATS $(ATSHOMEQ)/src

CCFLAGS=-fPIC -O2
INCLUDES=-I$(ATSHOMEQ)

######

SOURCES = \
  atsyntax_util.sats \
  atsyntax_util.dats \

OBJECTS := $(patsubst %.sats, %_sats.o, $(SOURCES))
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))

######

ATSLIB=$(ATSHOMEQ)/ccomp/lib
ATSLIB=$(ATSHOMEQ)/ccomp/lib64

######

all:: libatsyntax
all:: cleanall

######

libatsyntax: $(OBJECTS)
	$(ATSCC) -fPIC -shared -o $(ATSLIB)/libatsyntax.so -Wl,-soname,libatsyntax.so `ar t libatsyntax.a`

######

AR=ar

######

atsyntax_util_sats.o: atsyntax_util.sats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyntax_util.sats
	$(AR) -r libatsyntax.a $@
atsyntax_util_dats.o: atsyntax_util.dats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyntax_util.dats
	$(AR) -r libatsyntax.a $@

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) libatsyntax.a

distclean:: cleanall

###### end of [Makefile] ######
