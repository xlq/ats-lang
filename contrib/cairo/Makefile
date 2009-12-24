#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: December, 2009
#

ATSCC="$(ATSHOME)"/bin/atscc

######

atsctrb_cairo.o: cairo_sats.o
	ld -r -o $@ cairo_sats.o

######

cairo_sats.o: SATS/cairo.sats
	atscc `pkg-config --cflags cairo` -o $@ -c SATS/cairo.sats

######

clean::
	rm -f cairo_sats.c cairo_sats.o

cleanall: clean
	rm -f atsctrb_cairo.o

###### end of [Makefile] ######
