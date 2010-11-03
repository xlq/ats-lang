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

compall:: fact

######

fact: fact.dats
	$(ATSCC) -D_ATS_PROOFCHECK -o fact fact.dats -lats && ./fact

######

html::
	$(ATSOPT) --posmark_html -d HelloWorld.dats > HelloWorld_dats.html
	$(ATSOPT) --posmark_html -d fact.dats > fact_dats.html

######

xref::
	$(ATSOPT) --posmark_xref=XREF -d \
          $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
	$(ATSOPT) --posmark_xref=XREF -d fact.dats > fact_dats.html

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

###### end of [Makefile] ######
