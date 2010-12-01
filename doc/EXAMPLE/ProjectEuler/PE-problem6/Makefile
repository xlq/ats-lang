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
compall:: problem6-hwxi
compall:: problem6-hwxi2

######

problem6-hwxi: problem6-hwxi.dats
	$(ATSCC) -O2 -o $@ $< && ./problem6-hwxi
problem6-hwxi2: problem6-hwxi2.dats
	$(ATSCC) -O2 -o $@ $< && ./problem6-hwxi2

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem6-hwxi
cleanall:: ; $(RMF) problem6-hwxi2
