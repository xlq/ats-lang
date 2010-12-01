##
## A simple Makefile
##

######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all
all:: checkall

######

checkall: compall cleanall

######

compall:: fib_mt
fib_mt: fib_mt.dats
	$(ATSCC) -o fib_mt -O3 -D_ATS_MULTITHREAD fib_mt.dats -lpthread

######

compall:: nsieve_mt
nsieve_mt: nsieve_mt.dats
	$(ATSCC) -o nsieve_mt -O3 -D_ATS_MULTITHREAD nsieve_mt.dats -lm -lpthread

compall:: nsieve2_mt
nsieve2_mt: nsieve2_mt.dats
	$(ATSCC) -o nsieve2_mt -O3 -D_ATS_MULTITHREAD nsieve2_mt.dats -lm -lpthread

######

compall:: partial-sums_mt
partial-sums_mt: partial-sums_mt.dats
	$(ATSCC) -o partial-sums_mt -O3 -D_ATS_MULTITHREAD partial-sums_mt.dats -lm -lpthread

######

compall:: qsort_mt_flt
qsort_mt_flt: qsort_mt_flt.dats
	$(ATSCC) -o qsort_mt_flt -O3 -D_ATS_MULTITHREAD qsort_mt_flt.dats -lm -lpthread

compall:: qsort_mt_int
qsort_mt_int: qsort_mt_int.dats
	$(ATSCC) -o qsort_mt_int -O3 -D_ATS_MULTITHREAD qsort_mt_int.dats -lm -lpthread

######

compall:: randcompec_mt
randcompec_mt: randcompec_mt.dats
	$(ATSCC) -o randcompec_mt -O3 -D_ATS_MULTITHREAD randcompec_mt.dats -lpthread

compall:: randcompec2_mt
randcompec2_mt: randcompec2_mt.dats
	$(ATSCC) -o randcompec2_mt -O3 -D_ATS_MULTITHREAD randcompec2_mt.dats -lpthread

compall:: randcompec3_mt
randcompec3_mt: randcompec3_mt.dats
	$(ATSCC) -o randcompec3_mt -O3 -D_ATS_MULTITHREAD randcompec3_mt.dats -lpthread

######

xref:: ; $(ATSOPT) --posmark_xref=XREF -d \
  $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
xref:: ; $(ATSOPT) --posmark_xref=XREF -d fib_mt.dats > fib_mt_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d nsieve_mt.dats > nsieve_mt_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d nsieve2_mt.dats > nsieve2_mt_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d partial-sums_mt.dats > partial-sums_mt_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d qsort_mt.dats > qsort_mt_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d qsort_mt_int.dats > qsort_mt_int_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d qsort_mt_flt.dats > qsort_mt_flt_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d randcompec_mt.dats > randcompec_mt_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d randcompec2_mt.dats > randcompec2_mt_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d randcompec3_mt.dats > randcompec3_mt_dats.html

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c

cleanall:: clean
	$(RMF) ./*_?ats.html
	$(RMF) ./XREF/*.html
cleanall::
	$(RMF) fib_mt
	$(RMF) nsieve_mt
	$(RMF) nsieve2_mt
	$(RMF) partial-sums_mt
	$(RMF) qsort_mt_flt
	$(RMF) qsort_mt_int
	$(RMF) randcompec_mt
	$(RMF) randcompec2_mt
	$(RMF) randcompec3_mt

###### end of [Makefile] ######
