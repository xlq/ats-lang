#
# API for GTK in ATS
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: May, 2010
#

######

ATSCC="$(ATSHOME)"/bin/atscc
GTKCFLAGS = `pkg-config gtk+-2.0 --cflags`

######

all: atsctrb_GTK.o clean

######

atsctrb_GTK.o: GTK_dats.o
	ld -r -o $@ GTK_dats.o

######

GTK_dats.o: DATS/gtk.dats
	$(ATSCC) $(GTKCFLAGS) -o $@ -c DATS/gtk.dats

######

clean::
	rm -f *_?ats.c *_?ats.o

cleanall: clean
	rm -f atsctrb_GTK.o

###### end of [Makefile] ######
