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

.PHONY: all

# ######

all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: clapack_test
clapack_test: clapack_test.dats
	$(ATSCC) $(LIBFLAGS) -O3 -o $@ $< $(ATSCTRB) -llapack -lcblas \
      && ./clapack_test
cleanall:: ; $(RMF) clapack_test

######

html:: ; $(ATSOPT) --posmark_html -d clapack_test.dats > clapack_test_dats.html
cleanall:: ; $(RMF) clapack_test_dats.html

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

###### end of [Makefile] ######
