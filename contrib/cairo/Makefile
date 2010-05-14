#
# API for cairo in ATS
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: December, 2009
#

ATSCC="$(ATSHOME)"/bin/atscc
XRCFLAGS=`pkg-config cairo --cflags --libs`

######

all: atsctrb_cairo.o clean

######

atsctrb_cairo.o: cairo_dats.o
	ld -r -o $@ cairo_dats.o

######

cairo_dats.o: DATS/cairo.dats
	$(ATSCC) $(XRCFLAGS) -o $@ -c DATS/cairo.dats

######

clean::
	rm -f *_?ats.c *_?ats.o

cleanall: clean
	rm -f atsctrb_cairo.o

###### end of [Makefile] ######
