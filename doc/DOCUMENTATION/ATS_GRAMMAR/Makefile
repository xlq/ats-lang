#
#
# A simple Makefile for documenting the grammar of ATS
#
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt
######

ATSGCFLAG=-D_ATS_GCATS

######

OBJECT := \
  atsgrammar_sats.o \
  atsgrammar_symbol_dats.o \
  atsgrammar_grmrule_dats.o \
  atsgrammar_main_dats.o \

######

atsgrammar: $(OBJECT); $(ATSCC) $(ATSGCFLAG) -o $@ $(OBJECT)

######

atsgrammar_sats.o: atsgrammar.sats
	$(ATSCC) -c -o $@ $<

atsgrammar_symbol_dats.o: atsgrammar_symbol.dats
	$(ATSCC) -c -o $@ $<

atsgrammar_grmrule_dats.o: atsgrammar_grmrule.dats
	$(ATSCC) -c -o $@ $<

atsgrammar_main_dats.o: atsgrammar_main.dats
	$(ATSCC) -c -o $@ $<

######

#
# HX: '-o .depend' means appending instead of overwriting
#
depend::
	rm -f .depend
	$(ATSOPT) -o .depend -dep1 -s atsgrammar.sats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_symbol.dats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_grmrule.dats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_main.dats
include .depend

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) atsgrammar

###### end of [Makefile] ######