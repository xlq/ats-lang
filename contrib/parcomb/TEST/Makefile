######
#
# Makefile for parcomb testing
#
######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSCTRB=$(ATSHOMEQ)/contrib/parcomb/atsctrb_parcomb.o

######

.PHONY: all

######

all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: calc1
calc1: calc1_example.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< $(ATSCTRB)
cleanall:: ; $(RMF) calc1

checkall:: calc2
calc2: calc2_example.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< $(ATSCTRB)
cleanall:: ; $(RMF) calc2

checkall:: calc3
calc3: calc3_example.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< $(ATSCTRB)
cleanall:: ; $(RMF) calc3

######

checkall:: lambda
lambda: lambda_example.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< $(ATSCTRB)
cleanall:: ; $(RMF) lambda

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

###### end of [Makefile] ######
