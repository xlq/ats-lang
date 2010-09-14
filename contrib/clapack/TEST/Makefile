#
#
# Makefile for some BLAS testing code 
#
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt
LIBFLAGS=-L/usr/lib/atlas -L/usr/lib64/atlas
ATSCTRB=\
  $(ATSHOMEQ)/contrib/cblas/atsctrb_cblas.o \
  $(ATSHOMEQ)/contrib/clapack/atsctrb_clapack.o \

######

checkall: test cleanall

######

test: clapack_test.dats
	$(ATSCC) $(LIBFLAGS) -O3 -o test clapack_test.dats $(ATSCTRB) -llapack -lcblas \
      && ./test

######

html::
	$(ATSOPT) --posmark_html -d clapack_test.dats > clapack_test_dats.html

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f test
	rm -f *_?ats.html


###### end of [Makefile] ######
