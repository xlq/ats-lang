######
#
# A simple Makefile
#
######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem5-hwxi \

######

problem5-hwxi: problem5-hwxi.dats
	$(ATSCC) -o $@ problem5-hwxi.dats -lats -lgmp && ./problem5-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem5-hwxi

###### end of [Makefile] ######
