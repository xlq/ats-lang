#
# A simple Makefile
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

problem4: problem4.dats ; $(ATSCC) -tc $<
cleanall:: ; $(RMF) problem4

######

RMF=rm -f

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c *_?ats.o

cleanall:: clean

###### end of [Makefile] ######
