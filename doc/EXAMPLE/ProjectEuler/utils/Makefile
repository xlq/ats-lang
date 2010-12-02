#
# A simple Makefile
#

######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc

######

#
# HX-2010-12-01:
# this command is used to generate Makefiles
# for individual PE problems
#
makefilegen: makefilegen.sats makefilegen.dats
	$(ATSCC) -o $@ -O2 makefilegen.sats makefilegen.dats

######

RMF=rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) makefilegen

###### end of [Makefile] ######
