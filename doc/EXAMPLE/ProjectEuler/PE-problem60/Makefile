######
#
# A simple Makefile
#
######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(or $(ATSHOMEQ), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem60-hwxi \

######

problem60-hwxi: problem60-hwxi.dats
	$(ATSCC) -g -D_ATS_GCATS -O2 -o $@ problem60-hwxi.dats -lm && ./problem60-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem60-hwxi

###### end of [Makefile] ######
