#
#
# Some introductory examples written in ATS
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

compall: \
  HelloWorld f91 fact1 fact2 fact3 fibs revarr revstr

HelloWorld: HelloWorld.dats
	$(ATSCC) -o HelloWorld HelloWorld.dats && ./HelloWorld

f91: f91.dats
	$(ATSCC) -o f91 f91.dats && ./f91 0

fact1: fact1.dats
	$(ATSCC) -o fact1 fact1.dats && ./fact1 10

fact2: fact2.dats
	$(ATSCC) -o fact2 fact2.dats && ./fact2 10

fact3: fact3.dats
	$(ATSCC) -D_ATS_PROOFCHECK -o fact3 fact3.dats -lats -lgmp && ./fact3 100

fact4: fact4.dats
	$(ATSCC) -D_ATS_PROOFCHECK -o fact4 fact4.dats -lats -lgmp && ./fact4 10

fact_in_c: fact_in_c.dats
	$(ATSCC) -o fact_in_c fact_in_c.dats && ./fact_in_c 10

fibs: fibs.dats
	$(ATSCC) -o fibs fibs.dats -lats -lgmp && ./fibs 20

revarr: revarr.dats
	$(ATSCC) -o revarr revarr.dats && ./revarr

revstr: revstr.dats
	$(ATSCC) -o revstr revstr.dats && ./revstr "abcdefghijklmnopqrstuvwxyz"

tally: tally.dats
	$(ATSCC) -o tally tally.dats -lats && ./tally

######

html::
	$(ATSOPT) --posmark_html -d HelloWorld.dats > HelloWorld_dats.html
	$(ATSOPT) --posmark_html -d f91.dats > f91_dats.html
	$(ATSOPT) --posmark_html -d fact1.dats > fact1_dats.html
	$(ATSOPT) --posmark_html -d fact2.dats > fact2_dats.html
	$(ATSOPT) --posmark_html -d fact3.dats > fact3_dats.html
	$(ATSOPT) --posmark_html -d fact4.dats > fact4_dats.html
	$(ATSOPT) --posmark_html -d fact_in_c.dats > fact_in_c_dats.html
	$(ATSOPT) --posmark_html -d fibs.dats > fibs_dats.html
	$(ATSOPT) --posmark_html -d revarr.dats > revarr_dats.html
	$(ATSOPT) --posmark_html -d revstr.dats > revstr_dats.html
	$(ATSOPT) --posmark_html -d tally.dats > tally_dats.html

######

clean::
	rm -f ./INTRO/*
	rm -f *_dats.c *_sats.c *_dats.html *_sats.html *~

cleanall:: clean
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
