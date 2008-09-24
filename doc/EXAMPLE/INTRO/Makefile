#
#
# Some introductory examples 
#
#

######

all: HelloWorld f91 fact1 fact2 fact3 fibs

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

fibs: fibs.dats
	atscc -o fibs fibs.dats -lats -lgmp

######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/INTRO

update::
	cp Makefile $(DIR)
	cp f91.dats $(DIR)
	cp fact1.dats $(DIR)
	cp fact2.dats $(DIR)
	cp fact3.dats $(DIR)
	cp fact_in_c.dats $(DIR)
	cp fibs.dats $(DIR)
	cp HelloWorld.dats $(DIR)

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall:: clean
	if [ -f HelloWorld ] ; then rm HelloWorld ; fi
	if [ -f f91 ] ; then rm f91 ; fi
	if [ -f fact1 ] ; then rm fact1 ; fi
	if [ -f fact2 ] ; then rm fact2 ; fi
	if [ -f fact3 ] ; then rm fact3 ; fi
	if [ -f fibs ] ; then rm fibs ; fi
