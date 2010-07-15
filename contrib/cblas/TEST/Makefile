#
#
# Makefile for some BLAS testing code 
#
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt
LIBFLAGS=-L/usr/lib/atlas
ATSCTRB="$(ATSHOME)"/contrib/cblas/atsctrb_cblas.o

######

checkall: test cleanall

######

test: cblas_test.dats
	$(ATSCC) $(LIBFLAGS) -O3 -o test \
          cblas_test.dats $(ATSCTRB) -lcblas -lm \
        && ./test

######

html::
	$(ATSOPT) --posmark_html -d cblas_test.dats > cblas_test_dats.html

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f test
	rm -f *_?ats.html


###### end of [Makefile] ######
