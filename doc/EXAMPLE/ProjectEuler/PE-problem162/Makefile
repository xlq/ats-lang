#
# Time of Generation: Tue Dec 14 22:22:27 2010
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
compall:: problem162-hwxi

######

problem162-hwxi: problem162-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lats -lgmp && ./problem162-hwxi

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem162-hwxi
