#
# A simple Makefile
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.6"
endif # end of [ifeq]

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRB=$(ATSLIBQ)/contrib/GL/atsctrb_graphviz.o

######

LDFLAGS=-lgsl -lgslcblas

######

cleanall:: clean

######

test_rng: test_rng.dats ; $(ATSCC) -o $@ $< $(LDFLAGS) 
cleanall:: ; $(RMF) test_rng

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c
clean:: ; $(RMF) *_?ats.o

###### end of [Makefile] ######
