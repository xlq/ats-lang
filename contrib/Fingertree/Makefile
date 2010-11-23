#
#
# A finger tree implementation in ATS
#
# Contributed by
#   Robbie Harwood (rharwood AT cs DOT bu DOT edu)
# Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

LD=ld
CCFLAG=-O2

######

all:: atsctrb_fingertree.o clean

######

atsctrb_fingertree.o: \
  fingertree_sats.o fingertree_dats.o
	$(LD) -r -o $@ $^

######

fingertree_sats.o: SATS/fingertree.sats
	$(ATSCC) $(CCFLAG) -o $@ -c $<
fingertree_dats.o: DATS/fingertree.dats
	$(ATSCC) $(CCFLAG) -o $@ -c $<

######

RMF = rm -f

######

clean::
	rm -f *_?ats.c *_?ats.o

cleanall: clean
	rm -f atsctrb_fingertree.o

###### end of [Makefile] ######
