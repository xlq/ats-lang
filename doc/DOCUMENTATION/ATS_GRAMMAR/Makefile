#
#
# A simple Makefile for documenting the grammar of ATS
#
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

OBJECT := \
  atsgrammar_sats.o \
  atsgrammar_symbol_dats.o \
  atsgrammar_grmrule_dats.o \
  atsgrammar_main_dats.o \

######

atsgrammar: $(OBJECT); $(ATSCC) -o $@ $(OBJECT)

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

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean

###### end of [Makefile] ######