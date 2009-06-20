##
## Course: Concepts of Programming Languages (BU CAS CS 320)
## Semester: Summer I, 2009
## Instructor: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
##

##
## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Time: June, 2009
##

######

CCFLAGS=
CCFLAGS=-g
GCFLAG=-D_ATS_GCATS

######

stfpl: \
  stfpl_main_dats.o \
  error_sats.o error_dats.o \
  symbol_sats.o symbol_dats.o \
  absyn_sats.o absyn_dats.o \
  fixity_sats.o fixity_dats.o \
  parser_sats.o parser_dats.o \
  trans1_sats.o trans1_dats.o \
  posloc_sats.o posloc_dats.o \
  tokenize_sats.o tokenize_dats.o \
  parcomb_sats.o parcomb_dats.o \
  hashtable_dats.o \

	atscc $(GCFLAG) -o stfpl \
  stfpl_main_dats.o \
  error_sats.o error_dats.o \
  symbol_sats.o symbol_dats.o \
  absyn_sats.o absyn_dats.o \
  fixity_sats.o fixity_dats.o \
  parser_sats.o parser_dats.o \
  trans1_sats.o trans1_dats.o \
  posloc_sats.o posloc_dats.o \
  tokenize_sats.o tokenize_dats.o \
  parcomb_sats.o parcomb_dats.o \
  hashtable_dats.o \

######

stfpl_main_dats.o: stfpl_main.dats
	atscc $(CCFLAGS) -c -o stfpl_main_dats.o stfpl_main.dats

######

error_sats.o: error.sats
	atscc $(CCFLAGS) -o error_sats.o -c error.sats

error_dats.o: error.dats
	atscc $(CCFLAGS) -o error_dats.o -c error.dats

######

symbol_sats.o: symbol.sats
	atscc $(CCFLAGS) -c -o symbol_sats.o symbol.sats

symbol_dats.o: symbol.dats
	atscc $(CCFLAGS) -c -o symbol_dats.o symbol.dats

######

absyn_sats.o: absyn.sats
	atscc $(CCFLAGS) -c -o absyn_sats.o absyn.sats

absyn_dats.o: absyn.dats
	atscc $(CCFLAGS) -c -o absyn_dats.o absyn.dats

######

fixity_sats.o: fixity.sats
	atscc $(CCFLAGS) -c -o fixity_sats.o fixity.sats

fixity_dats.o: fixity.dats
	atscc $(CCFLAGS) -c -o fixity_dats.o fixity.dats

######

parser_sats.o: parser.sats
	atscc $(CCFLAGS) -o parser_sats.o -c parser.sats

parser_dats.o: parser.dats
	atscc $(CCFLAGS) -IATS PARCOMB -o parser_dats.o -c parser.dats

######

trans1_sats.o: trans1.sats
	atscc $(CCFLAGS) -o trans1_sats.o -c trans1.sats

trans1_dats.o: trans1.dats
	atscc $(CCFLAGS) -IATS PARCOMB -o trans1_dats.o -c trans1.dats

######

posloc_sats.o: PARCOMB/posloc.sats
	atscc $(CCFLAGS) -c -o posloc_sats.o PARCOMB/posloc.sats

posloc_dats.o: PARCOMB/posloc.dats
	atscc $(CCFLAGS) -IATS PARCOMB -c -o posloc_dats.o PARCOMB/posloc.dats

parcomb_sats.o: PARCOMB/parcomb.sats
	atscc $(CCFLAGS) -c -o parcomb_sats.o PARCOMB/parcomb.sats

parcomb_dats.o: PARCOMB/parcomb.dats
	atscc $(CCFLAGS) -IATS PARCOMB -c -o parcomb_dats.o PARCOMB/parcomb.dats

tokenize_sats.o: PARCOMB/tokenize.sats
	atscc $(CCFLAGS) -IATS PARCOMB -c -o tokenize_sats.o PARCOMB/tokenize.sats

tokenize_dats.o: PARCOMB/tokenize.dats
	atscc $(CCFLAGS) -IATS PARCOMB -c -o tokenize_dats.o PARCOMB/tokenize.dats

######

hashtable_dats.o: HASHTABLE/hashtable.dats
	atscc $(CCFLAGS) -IATS HASHTABLE -c -o hashtable_dats.o HASHTABLE/hashtable.dats

######

ATSOPT=$(ATSHOME)/bin/atsopt

xref::
	$(ATSOPT) --posmark_xref=XREF \
          -d ats_prelude_xref.dats > /dev/null
	$(ATSOPT) --posmark_xref=XREF \
          -d stfpl_main.dats > stfpl_main_dats.html
	$(ATSOPT) --posmark_xref=XREF -d error.dats > error_dats.html
	$(ATSOPT) --posmark_xref=XREF -d symbol.dats > symbol_dats.html
	$(ATSOPT) --posmark_xref=XREF -d absyn.dats > absyn_dats.html
	$(ATSOPT) --posmark_xref=XREF -d parser.dats > parser_dats.html
	$(ATSOPT) --posmark_xref=XREF -d trans1.dats > trans1_dats.html

######

chmod::
	chmod 644 Makefile
	chmod 644 *.?ats
	chmod 644 *_?ats.html
	cd XREF; chmod 644 *.html

######

clean::
	rm -f *~
	rm -f *_sats.c *_dats.c
	rm -f *_sats.o *_dats.o

cleanall: clean
	rm -f stfpl
	rm -f *_?ats.html */*_?ats.html
	rm -f XREF/*.html

######

lines::
	wc -l *.?ats

###### end of [Makefile] ######
