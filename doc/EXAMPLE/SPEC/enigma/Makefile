#
# A simple make file
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all

all: checkall cleanall

######

checkall:: test

######

test: test.dats
	$(ATSCC) -o $@ test.dats enigma.sats enigma.dats && ./test
cleanall:: ; $(RMF) test

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean

###### end of [Makefile] ######