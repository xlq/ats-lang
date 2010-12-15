#
# Time of Generation: Tue Dec 14 22:22:26 2010
#

######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif
ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt

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
