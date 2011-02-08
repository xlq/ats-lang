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

ATSCC=$(ATSHOME)/bin/atscc

######

CCFLAGS=-O2 -g
#CCFLAGS=
GCFLAG=-D_ATS_GCATS
#GCFLAG=

######

LIBPARCOMB=$(ATSHOME)/contrib/parcomb/atsctrb_parcomb.o

######

SOURCES=\
  stfpl_main.dats \
  error.sats error.dats \
  symbol.sats symbol.dats \
  absyn.sats absyn.dats \
  fixity.sats fixity.dats \
  parser.sats parser.dats \
  trans1.sats trans1.dats \
  interp.sats interp.dats \

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))

######

stfpl: $(OBJECTS)
	$(ATSCC) $(GCFLAG) -o stfpl $(OBJECTS) $(LIBPARCOMB)

######

test:: stfpl
	./stfpl < TEST/f91.stfpl
	./stfpl < TEST/fact.stfpl
	./stfpl < TEST/fact_fix.stfpl
	./stfpl < TEST/fib.stfpl
	./stfpl < TEST/twice.stfpl
	./stfpl < TEST/queens.stfpl

######

stfpl_main_dats.o: stfpl_main.dats
	$(ATSCC) $(CCFLAGS) -c -o stfpl_main_dats.o stfpl_main.dats

######

error_sats.o: error.sats
	$(ATSCC) $(CCFLAGS) -o error_sats.o -c error.sats

error_dats.o: error.dats
	$(ATSCC) $(CCFLAGS) -o error_dats.o -c error.dats

######

symbol_sats.o: symbol.sats; $(ATSCC) $(CCFLAGS) -c -o $@ symbol.sats
symbol_dats.o: symbol.dats; $(ATSCC) $(CCFLAGS) -c -o $@ symbol.dats

######

absyn_sats.o: absyn.sats; $(ATSCC) $(CCFLAGS) -c -o $@ absyn.sats
absyn_dats.o: absyn.dats; $(ATSCC) $(CCFLAGS) -c -o $@ absyn.dats

######

fixity_sats.o: fixity.sats; $(ATSCC) $(CCFLAGS) -c -o $@ fixity.sats
fixity_dats.o: fixity.dats; $(ATSCC) $(CCFLAGS) -c -o $@ fixity.dats

######

parser_sats.o: parser.sats; $(ATSCC) $(CCFLAGS) -o $@ -c parser.sats
parser_dats.o: parser.dats; $(ATSCC) $(CCFLAGS) -o $@ -c parser.dats

######

trans1_sats.o: trans1.sats; $(ATSCC) $(CCFLAGS) -o $@ -c trans1.sats
trans1_dats.o: trans1.dats; $(ATSCC) $(CCFLAGS) -o $@ -c trans1.dats

######

interp_sats.o: interp.sats; $(ATSCC) $(CCFLAGS) -o $@ -c interp.sats
interp_dats.o: interp.dats; $(ATSCC) $(CCFLAGS) -o $@ -c interp.dats

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
	$(ATSOPT) --posmark_xref=XREF -d interp.dats > interp_dats.html

######

chmod::
	chmod 644 Makefile
	chmod 644 *.?ats
	chmod 644 *_?ats.html
	cd XREF; chmod 644 *.html

######

#
#svn propdel svn:externals .
#svn propset svn:externals . --file [a_file_containing_the_following_line]
#PARCOMB https://ats-lang.svn.sourceforge.net/svnroot/ats-lang/contrib/parcomb
#

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_sats.c *_dats.c
	$(RMF) *_sats.o *_dats.o

cleanall: clean
	$(RMF) stfpl
	$(RMF) *_?ats.html */*_?ats.html
	$(RMF) XREF/*.html

######

lines::
	wc -l *.?ats

###### end of [Makefile] ######
