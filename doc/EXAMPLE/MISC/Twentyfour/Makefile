##
## Makefile for [twentyfour.dats]
##

######
  
ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

#GCFLAG=-D_ATS_gc // no longer in use
#GCFLAG=-D_ATS_gcats // no longer in use
GCFLAG=-D_ATS_GCATS
#GCFLAG=-D_ATS_GCBDW

######

.PHONY: all
all: checkall

######

checkall:: twentyfour cleanall

######

twentyfour: twentyfour.dats rational.dats rational.sats
	$(ATSCC) -O2 $(GCFLAG) -o twentyfour twentyfour.dats rational.dats rational.sats -lm \
     && ./twentyfour
######

clean:: ; rm -f *_dats.c *_sats.c *~
cleanall: clean; rm -f twentyfour

###### end of [Makefile] ######
