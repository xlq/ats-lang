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
  problem45-hwxi \

######

problem45-hwxi: problem45-hwxi.dats
	$(ATSCC) -O3 -o $@ problem45-hwxi.dats -lm && ./problem45-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem45-hwxi

###### end of [Makefile] ######
