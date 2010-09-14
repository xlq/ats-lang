#
# API for pango in ATS
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: May, 2010
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
PANGOCFLAGS=`pkg-config pango --cflags`

######

all: atsctrb_pango.o clean

######

atsctrb_pango.o: pango_dats.o
	ld -r -o $@ pango_dats.o

######

pango_dats.o: DATS/pango.dats
	$(ATSCC) $(PANGOCFLAGS) -o $@ -c DATS/pango.dats

######

clean::
	rm -f *_?ats.c *_?ats.o

cleanall: clean
	rm -f atsctrb_pango.o

###### end of [Makefile] ######
