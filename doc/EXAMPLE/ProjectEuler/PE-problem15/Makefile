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
compall:: problem15-hwxi
compall:: problem15-hwxi2
compall:: problem15-mberndt

######

problem15-hwxi: problem15-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lats -lgmp && ./problem15-hwxi
problem15-hwxi2: problem15-hwxi2.dats
	$(ATSCC) -O2 -o $@ $< && ./problem15-hwxi2
problem15-mberndt: problem15-mberndt.dats
	$(ATSCC) -O2 -o $@ $< && ./problem15-mberndt

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem15-hwxi
cleanall:: ; $(RMF) problem15-hwxi2
cleanall:: ; $(RMF) problem15-mberndt
