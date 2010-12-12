#
#
# Some examples in ATS involving syndef-loaded identifiers
#
#

######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all
all: checkall

######

checkall: compall cleanall

######

compall:: fact
fact: fact.dats
	$(ATSCC) -o fact fact.dats -ldl -lats && ./fact

compall:: forlist
forlist: forlist.dats
	$(ATSCC) -o forlist forlist.dats -ldl -lats && ./forlist

compall:: forrange
forrange: forrange.dats
	$(ATSCC) -o forrange forrange.dats -ldl -lats && ./forrange

######

html:: ; $(ATSOPT) --posmark_html -d fact.dats > fact_dats.html
html:: ; $(ATSOPT) --posmark_html -d forlist.dats > forlist_dats.html
html:: ; $(ATSOPT) --posmark_html -d forrange.dats > forrange_dats.html

######

xref:: ; $(ATSOPT) --posmark_xref=XREF -d \
  $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
xref:: ; $(ATSOPT) --posmark_xref=XREF -d fact.dats > fact_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d forlist.dats > forlist_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d forrange.dats > forrange_dats.html

######

RMF=rm -f

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
	$(RMF) forrange

###### end of [Makefile] ######
