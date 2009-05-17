#
#
# Some introductory examples 
#
#

######

checkall: compall cleanall

######

compall: \
  HelloWorld f91 fact1 fact2 fact3 fibs revarr revstr

HelloWorld: HelloWorld.dats
	atscc -o HelloWorld HelloWorld.dats

f91: f91.dats
	atscc -o f91 f91.dats

fact1: fact1.dats
	atscc -o fact1 fact1.dats

fact2: fact2.dats
	atscc -o fact2 fact2.dats

fact3: fact3.dats
	atscc -o fact3 fact3.dats -lats -lgmp

fact_in_c: fact_in_c.dats
	atscc -o fact_in_c fact_in_c.dats

fibs: fibs.dats
	atscc -o fibs fibs.dats -lats -lgmp

revarr: revarr.dats
	atscc -o revarr revarr.dats

revstr: revstr.dats
	atscc -o revstr revstr.dats

######

html::
	atsopt --posmark_html -d HelloWorld.dats > HelloWorld_dats.html
	atsopt --posmark_html -d f91.dats > f91_dats.html
	atsopt --posmark_html -d fact1.dats > fact1_dats.html
	atsopt --posmark_html -d fact2.dats > fact2_dats.html
	atsopt --posmark_html -d fact3.dats > fact3_dats.html
	atsopt --posmark_html -d fact_in_c.dats > fact_in_c_dats.html
	atsopt --posmark_html -d fibs.dats > fibs_dats.html
	atsopt --posmark_html -d revarr.dats > revarr_dats.html
	atsopt --posmark_html -d revstr.dats > revstr_dats.html

######

clean::
	rm -f INTRO/*
	rm -f *_dats.c *_sats.c *_dats.html *_sats.html *~

cleanall:: clean
	if [ -f HelloWorld ] ; then rm HelloWorld ; fi
	if [ -f f91 ] ; then rm f91 ; fi
	if [ -f fact1 ] ; then rm fact1 ; fi
	if [ -f fact2 ] ; then rm fact2 ; fi
	if [ -f fact3 ] ; then rm fact3 ; fi
	if [ -f fact_in_c ] ; then rm fact_in_c ; fi
	if [ -f fibs ] ; then rm fibs ; fi
	if [ -f revarr ] ; then rm revarr ; fi
	if [ -f revstr ] ; then rm revstr ; fi

###### end of [Makefile] ######
