######
#
# Makefile for parcomb testing
#
######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSCTRB=$(ATSHOMEQ)/contrib/parcomb/atsctrb_parcomb.o

######

checkall:: compall cleanall

compall:: \
  calc1 calc2 calc3 lambda

######

calc1: calc1_example.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< $(ATSCTRB)

calc2: calc2_example.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< $(ATSCTRB)

calc3: calc3_example.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< $(ATSCTRB)

######

lambda: lambda_example.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< $(ATSCTRB)

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall: clean
	$(RMF) calc1
	$(RMF) calc2
	$(RMF) calc3
	$(RMF) lambda

###### end of [Makefile] ######
