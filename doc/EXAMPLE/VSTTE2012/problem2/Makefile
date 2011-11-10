#
# A simple Makefile
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

problem2: problem2.dats ; $(ATSCC) -o $@ $< && ./$@
cleanall:: ; $(RMF) problem2

######

RMF=rm -f

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c *_?ats.o

cleanall:: clean

###### end of [Makefile] ######
