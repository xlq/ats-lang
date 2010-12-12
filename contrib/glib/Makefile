#
# API for glib in ATS
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: February, 2010
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc -Wall

######

GCC=gcc

######

GLIBINC := -I"/usr/lib/glib-2.0/include"
GLIBINC += -I"/usr/lib64/glib-2.0/include"
INCLUDES= $(GLIBINC) -I"/usr/include/glib-2.0"

######

all:: glibconfig atsctrb_glib.o clean

######

glibconfig:: HATS/glibconfig
	$(GCC) $(INCLUDES) -E -P -o HATS/glibconfig.hats -x c HATS/glibconfig

######

atsctrb_glib.o: \
  glib_sats.o glib_dats.o
	ld -r -o $@ \
  glib_sats.o glib_dats.o

######

glib_sats.o: SATS/glib.sats
	$(ATSCC) $(INCLUDES) -o $@ -c SATS/glib.sats

glib_dats.o: DATS/glib.dats
	$(ATSCC) $(INCLUDES) -o $@ -c DATS/glib.dats

######

clean::
	rm -f glib_sats.c glib_sats.o
	rm -f glib_dats.c glib_dats.o

cleanall: clean
	rm -f atsctrb_glib.o

###### end of [Makefile] ######
