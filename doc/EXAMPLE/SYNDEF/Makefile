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
  println \

######

fact: fact.dats
	$(ATSCC) -o fact fact.dats -lats && ./fact

forlist: forlist.dats
	$(ATSCC) -o forlist forlist.dats -lats && ./forlist

println: println.dats
	$(ATSCC) -o println println.dats -lats && ./println

######

html::
	$(ATSOPT) --posmark_html -d fact.dats > fact_dats.html
	$(ATSOPT) --posmark_html -d forlist.dats > forlist_dats.html

######

xref::
	$(ATSOPT) --posmark_xref=XREF -d \
          $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
	$(ATSOPT) --posmark_xref=XREF -d fact.dats > fact_dats.html
	$(ATSOPT) --posmark_xref=XREF -d forlist.dats > forlist_dats.html
	$(ATSOPT) --posmark_xref=XREF -d println.dats > println_dats.html

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
	$(RMF) forlist
	$(RMF) println

###### end of [Makefile] ######
