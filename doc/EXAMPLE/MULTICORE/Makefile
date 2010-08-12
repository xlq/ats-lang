##
## A simple Makefile
##

######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

.PHONY: all
all:: checkall

######

checkall:: compall cleanall

compall:: \
  fib_mt \
  nsieve_mt nsieve2_mt \
  partial-sums_mt \
  qsort_mt_flt \
  qsort_mt_int \
  randcompec_mt \

######

fib_mt: fib_mt.dats
	$(ATSCC) -o fib_mt -O3 -D_ATS_MULTITHREAD fib_mt.dats -lpthread

######

nsieve_mt: nsieve_mt.dats
	$(ATSCC) -o nsieve_mt -O3 -D_ATS_MULTITHREAD nsieve_mt.dats -lm -lpthread

nsieve2_mt: nsieve2_mt.dats
	$(ATSCC) -o nsieve2_mt -O3 -D_ATS_MULTITHREAD nsieve2_mt.dats -lm -lpthread

######

partial-sums_mt: partial-sums_mt.dats
	$(ATSCC) -o partial-sums_mt -O3 -D_ATS_MULTITHREAD partial-sums_mt.dats -lm -lpthread

######

qsort_mt_flt: qsort_mt_flt.dats
	$(ATSCC) -o qsort_mt_flt -O3 -D_ATS_MULTITHREAD qsort_mt_flt.dats -lm -lpthread

qsort_mt_int: qsort_mt_int.dats
	$(ATSCC) -o qsort_mt_int -O3 -D_ATS_MULTITHREAD qsort_mt_int.dats -lm -lpthread

######

randcompec_mt: randcompec_mt.dats
	$(ATSCC) -o randcompec_mt -O3 -D_ATS_MULTITHREAD randcompec_mt.dats -lpthread

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall: clean
	rm -f a.out
	rm -f fib_mt
	rm -f nsieve_mt
	rm -f nsieve2_mt
	rm -f partial-sums_mt
	rm -f qsort_mt_flt
	rm -f qsort_mt_int
	rm -f randcompec_mt

###### end of [Makefile] ######
