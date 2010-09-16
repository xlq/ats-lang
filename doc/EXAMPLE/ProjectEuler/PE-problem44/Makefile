######
#
# A simple Makefile
#
######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem44-hwxi \

######

problem44-hwxi: problem44-hwxi.dats
	$(ATSCC) -O3 -o $@ problem44-hwxi.dats -lm && ./problem44-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem44-hwxi

###### end of [Makefile] ######
