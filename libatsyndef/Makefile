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
  atsyndef_util.sats \
  atsyndef_util.dats \
  atsyndef_main.dats \

OBJECTS := $(patsubst %.sats, %_sats.o, $(SOURCES))
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))

######

ATSLIB=$(ATSHOMEQ)/ccomp/lib

######

libatsyndef: $(OBJECTS)
	gcc -shared -o $(ATSLIB)/libatsyndef.so -Wl,-soname,libatsyndef.so `ar t ${ATSHOME}/ccomp/lib/libatsyndef.a`

######

AR = ar
ATSLIB=$(ATSHOMEQ)/ccomp/lib

######

atsyndef_util_sats.o: atsyndef_util.sats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyndef_util.sats
	$(AR) -r $(ATSLIB)/libatsyndef.a $@
atsyndef_util_dats.o: atsyndef_util.dats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyndef_util.dats
	$(AR) -r $(ATSLIB)/libatsyndef.a $@

atsyndef_main_dats.o: atsyndef_main.dats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyndef_main.dats
	$(AR) -r $(ATSLIB)/libatsyndef.a $@

######

clean::
	rm -f *_sats.c *_dats.c *.o *~

cleanall: clean

###### end of [Makefile] ######
