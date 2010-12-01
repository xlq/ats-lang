#
#
# Some introductory examples written in ATS
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

compall:: HelloWorld
HelloWorld: HelloWorld.dats
	$(ATSCC) -o HelloWorld HelloWorld.dats && ./HelloWorld

compall:: f91
f91: f91.dats
	$(ATSCC) -o f91 f91.dats && ./f91 0

compall:: fact1
fact1: fact1.dats
	$(ATSCC) -o fact1 fact1.dats && ./fact1 10

compall:: fact2
fact2: fact2.dats
	$(ATSCC) -o fact2 fact2.dats && ./fact2 10

compall:: fact3
fact3: fact3.dats
	$(ATSCC) -D_ATS_PROOFCHECK -o fact3 fact3.dats -lats -lgmp && ./fact3 100

compall:: fact4
fact4: fact4.dats
	$(ATSCC) -D_ATS_PROOFCHECK -o fact4 fact4.dats -lats -lgmp && ./fact4 10

compall:: fact_in_c
fact_in_c: fact_in_c.dats
	$(ATSCC) -o fact_in_c fact_in_c.dats && ./fact_in_c 10

compall:: fibs
fibs: fibs.dats
	$(ATSCC) -o fibs fibs.dats -lats -lgmp && ./fibs 20

compall:: revarr
revarr: revarr.dats
	$(ATSCC) -o revarr revarr.dats && ./revarr

compall:: revstr
revstr: revstr.dats
	$(ATSCC) -o revstr revstr.dats && ./revstr "abcdefghijklmnopqrstuvwxyz"

compall:: tally
tally: tally.dats
	$(ATSCC) -o tally tally.dats -lats && ./tally

######

html:: ; $(ATSOPT) --posmark_html -d HelloWorld.dats > HelloWorld_dats.html
html:: ; $(ATSOPT) --posmark_html -d f91.dats > f91_dats.html
html:: ; $(ATSOPT) --posmark_html -d fact1.dats > fact1_dats.html
html:: ; $(ATSOPT) --posmark_html -d fact2.dats > fact2_dats.html
html:: ; $(ATSOPT) --posmark_html -d fact3.dats > fact3_dats.html
html:: ; $(ATSOPT) --posmark_html -d fact4.dats > fact4_dats.html
html:: ; $(ATSOPT) --posmark_html -d fact_in_c.dats > fact_in_c_dats.html
html:: ; $(ATSOPT) --posmark_html -d fibs.dats > fibs_dats.html
html:: ; $(ATSOPT) --posmark_html -d revarr.dats > revarr_dats.html
html:: ; $(ATSOPT) --posmark_html -d revstr.dats > revstr_dats.html
html:: ; $(ATSOPT) --posmark_html -d tally.dats > tally_dats.html

######

xref:: ; $(ATSOPT) --posmark_xref=XREF -d \
  $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
xref:: ; $(ATSOPT) --posmark_xref=XREF -d HelloWorld.dats > HelloWorld_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d f91.dats > f91_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d fact1.dats > fact1_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d fact2.dats > fact2_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d fact3.dats > fact3_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d fact4.dats > fact4_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d fact_in_c.dats > fact_in_c_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d fibs.dats > fibs_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d revarr.dats > revarr_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d revstr.dats > revstr_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d tally.dats > tally_dats.html

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
	if [ -f HelloWorld ] ; then rm HelloWorld ; fi
	if [ -f f91 ] ; then rm f91 ; fi
	if [ -f fact1 ] ; then rm fact1 ; fi
	if [ -f fact2 ] ; then rm fact2 ; fi
	if [ -f fact3 ] ; then rm fact3 ; fi
	if [ -f fact4 ] ; then rm fact4 ; fi
	if [ -f fact_in_c ] ; then rm fact_in_c ; fi
	if [ -f fibs ] ; then rm fibs ; fi
	if [ -f revarr ] ; then rm revarr ; fi
	if [ -f revstr ] ; then rm revstr ; fi
	if [ -f tally ] ; then rm tally ; fi

###### end of [Makefile] ######
