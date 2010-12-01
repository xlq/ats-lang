#
# Time of Generation: Wed Dec  1 16:24:57 2010
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
compall:: problem122-hwxi

######

problem122-hwxi: problem122-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lm && ./problem122-hwxi

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem122-hwxi
