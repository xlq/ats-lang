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
compall:: problem20-hwxi
compall:: problem20-hwxi2

######

problem20-hwxi: problem20-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lats -lgmp && ./problem20-hwxi
problem20-hwxi2: problem20-hwxi2.dats
	$(ATSCC) -O2 -o $@ $< && ./problem20-hwxi2

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem20-hwxi
cleanall:: ; $(RMF) problem20-hwxi2
