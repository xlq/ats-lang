#
#
# Makefile for some BLAS testing code 
#
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.3"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt
LIBFLAGS=-L/usr/lib/atlas -L/usr/lib64/atlas
ATSCTRB=$(ATSLIBQ)/contrib/cblas/atsctrb_cblas.o

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: cblas_test
cblas_test: cblas_test.dats
	$(ATSCC) $(LIBFLAGS) -O2 -o $@ cblas_test.dats $(ATSCTRB) -lcblas -lm \
     && ./cblas_test
cleanall:: ; $(RMF) cblas_test

######

checkall:: gemm_test1
gemm_test1: gemm_test1.dats
	$(ATSCC) $(LIBFLAGS) -O2 -o $@ gemm_test1.dats $(ATSCTRB) -lcblas -lm \
     && ./gemm_test1
cleanall:: ; $(RMF) gemm_test1

checkall:: gemm_test2
gemm_test2: gemm_test2.dats
	$(ATSCC) $(LIBFLAGS) -O2 -o $@ gemm_test2.dats $(ATSCTRB) -lcblas -lm \
     && ./gemm_test2
cleanall:: ; $(RMF) gemm_test2

######

checkall:: symm_test
symm_test: symm_test.dats
	$(ATSCC) $(LIBFLAGS) -O2 -o $@ symm_test.dats $(ATSCTRB) -lcblas -lm \
     && ./symm_test
cleanall:: ; $(RMF) symm_test

######

checkall:: lu_test
lu_test: lu_test.dats
	$(ATSCC) $(LIBFLAGS) -O2 -o $@ lu_test.dats $(ATSCTRB) -lcblas -lm \
     && ./lu_test
cleanall:: ; $(RMF) lu_test

######

html:: ; $(ATSOPT) --posmark_html -d cblas_test.dats > cblas_test_dats.html
cleanall:: ; $(RMF) *_?ats.html

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

###### end of [Makefile] ######
