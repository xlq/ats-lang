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
compall:: problem18-hwxi

######

problem18-hwxi: problem18-hwxi.dats
	$(ATSCC) -O2 -o $@ $< && ./problem18-hwxi

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem18-hwxi
