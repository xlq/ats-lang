#
#
# Some examples in ATS involving syndef-loaded identifiers
#
#

######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all
all: checkall

######

checkall: compall cleanall

######

compall:: \
  fact \
  forlist \
  forrange \

######

fact: fact.dats
	$(ATSCC) -o fact fact.dats -lats && ./fact

print: print.dats
	$(ATSCC) -o print print.dats -lats && ./print

forlist: forlist.dats
	$(ATSCC) -o forlist forlist.dats -lats && ./forlist

forrange: forrange.dats
	$(ATSCC) -o forrange forrange.dats -lats && ./forrange

######

html::
	$(ATSOPT) --posmark_html -d fact.dats > fact_dats.html
	$(ATSOPT) --posmark_html -d print.dats > print_dats.html
	$(ATSOPT) --posmark_html -d forlist.dats > forlist_dats.html
	$(ATSOPT) --posmark_html -d forrange.dats > forrange_dats.html

######

xref::
	$(ATSOPT) --posmark_xref=XREF -d \
          $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
	$(ATSOPT) --posmark_xref=XREF -d fact.dats > fact_dats.html
	$(ATSOPT) --posmark_xref=XREF -d print.dats > print_dats.html
	$(ATSOPT) --posmark_xref=XREF -d forlist.dats > forlist_dats.html
	$(ATSOPT) --posmark_xref=XREF -d forrange.dats > forrange_dats.html

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) ./INTRO/*
	$(RMF) *_dats.c *_sats.c

cleanall:: clean
	$(RMF) ./XREF/*
	$(RMF) *_?ats.html
	$(RMF) fact
	$(RMF) print
	$(RMF) forlist
	$(RMF) forrange

###### end of [Makefile] ######
