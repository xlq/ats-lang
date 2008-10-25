#
#
# Some introductory examples 
#
#

######

all: HelloWorld f91 fact1 fact2 fact3 fibs

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

HelloWorld: HelloWorld.dats
	atscc -o HelloWorld HelloWorld.dats

######

update::
	atsopt --posmark_html_only -d f91.dats
	atsopt --posmark_html_only -d fact1.dats
	atsopt --posmark_html_only -d fact2.dats
	atsopt --posmark_html_only -d fact3.dats
	atsopt --posmark_html_only -d fact_in_c.dats
	atsopt --posmark_html_only -d fibs.dats
	atsopt --posmark_html_only -d HelloWorld.dats

######

clean::
	rm -f INTRO/*
	rm -f *_dats.c *_sats.c *_dats.html *_sats.html *~

cleanall:: clean
	if [ -f f91 ] ; then rm f91 ; fi
	if [ -f fact1 ] ; then rm fact1 ; fi
	if [ -f fact2 ] ; then rm fact2 ; fi
	if [ -f fact3 ] ; then rm fact3 ; fi
	if [ -f fact_in_c ] ; then rm fact_in_c ; fi
	if [ -f fibs ] ; then rm fibs ; fi
	if [ -f HelloWorld ] ; then rm HelloWorld ; fi

###### end of [Makefile] ######
