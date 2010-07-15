#
# API for cblas in ATS
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: July, 2010
#

######

ATSCC="$(ATSHOME)"/bin/atscc -Wall
LIBFLAGS=-L/usr/lib/atlas

######

all: atsctrb_cblas.o clean

######

atsctrb_cblas.o: cblas_dats.o
	ld -r -o $@ cblas_dats.o

######

cblas_dats.o: DATS/cblas.dats
	$(ATSCC) $(LIBFLAGS) -o $@ -c DATS/cblas.dats

######

clean::
	rm -f *_?ats.c *_?ats.o

cleanall: clean
	rm -f atsctrb_cblas.o

###### end of [Makefile] ######
