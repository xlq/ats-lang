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
compall:: problem58-hwxi

######

problem58-hwxi: problem58-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lm && ./problem58-hwxi

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem58-hwxi
