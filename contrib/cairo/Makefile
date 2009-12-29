#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: December, 2009
#

ATSCC="$(ATSHOME)"/bin/atscc

######

all: atsctrb_cairo.o clean

######

atsctrb_cairo.o: cairo_sats.o cairo_dats.o
	ld -r -o $@ cairo_sats.o cairo_dats.o

######

cairo_sats.o: SATS/cairo.sats
	$(ATSCC) `pkg-config --cflags cairo` -o $@ -c SATS/cairo.sats

cairo_dats.o: DATS/cairo.dats
	$(ATSCC) `pkg-config --cflags cairo` -o $@ -c DATS/cairo.dats

######

clean::
	rm -f cairo_sats.c cairo_sats.o
	rm -f cairo_dats.c cairo_dats.o

cleanall: clean
	rm -f atsctrb_cairo.o

###### end of [Makefile] ######
