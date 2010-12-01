#
# Time of Generation: Wed Dec  1 16:24:56 2010
#

######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

checkall: compall cleanall
compall:: problem25-hwxi
compall:: problem25-hwxi2

######

problem25-hwxi: problem25-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lats -lgmp && ./problem25-hwxi
problem25-hwxi2: problem25-hwxi2.dats
	$(ATSCC) -O2 -o $@ $< && ./problem25-hwxi2

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem25-hwxi
cleanall:: ; $(RMF) problem25-hwxi2
