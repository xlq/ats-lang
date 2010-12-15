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
compall:: problem17-hwxi

######

problem17-hwxi: problem17-hwxi.dats
	$(ATSCC) -O2 -o $@ $< && ./problem17-hwxi

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem17-hwxi
