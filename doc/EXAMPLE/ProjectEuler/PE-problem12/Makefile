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
compall:: problem12-hwxi

######

problem12-hwxi: problem12-hwxi.dats
	$(ATSCC) -O2 -o $@ $< && ./problem12-hwxi

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem12-hwxi
