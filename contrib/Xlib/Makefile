#
# API for Xlib in ATS
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: January, 2010
#

ATSCC="$(ATSHOME)"/bin/atscc

######

all: atsctrb_Xlib.o clean

######

atsctrb_Xlib.o: Xlib_sats.o Xlib_dats.o
	ld -r -o $@ Xlib_sats.o Xlib_dats.o

######

Xlib_sats.o: SATS/Xlib.sats
	$(ATSCC) -IX11 -o $@ -c SATS/Xlib.sats

Xlib_dats.o: DATS/Xlib.dats
	$(ATSCC) -IX11 -o $@ -c DATS/Xlib.dats

######

clean::
	rm -f Xlib_sats.c Xlib_sats.o
	rm -f Xlib_dats.c Xlib_dats.o

cleanall: clean
	rm -f atsctrb_Xlib.o

###### end of [Makefile] ######
