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
	$(ATSCC) $(LIBFLAGS) -O2 -o $@ cblas_test.dats $(ATSCTRB) -lcblas -lm \
     && ./test

######

gemm_test1: gemm_test1.dats
	$(ATSCC) $(LIBFLAGS) -O2 -o $@ gemm_test1.dats $(ATSCTRB) -lcblas -lm \
     && ./gemm_test1

gemm_test2: gemm_test2.dats
	$(ATSCC) $(LIBFLAGS) -O2 -o $@ gemm_test2.dats $(ATSCTRB) -lcblas -lm \
     && ./gemm_test2

######

symm_test: symm_test.dats
	$(ATSCC) $(LIBFLAGS) -O2 -o $@ symm_test.dats $(ATSCTRB) -lcblas -lm \
     && ./symm_test

######

html::
	$(ATSOPT) --posmark_html -d cblas_test.dats > cblas_test_dats.html

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f test
	rm -f gemm_test1
	rm -f gemm_test2
	rm -f symm_test
	rm -f *_?ats.html


###### end of [Makefile] ######
