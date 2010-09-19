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
  problem25-hwxi \
  problem25-hwxi2 \

######

problem25-hwxi: problem25-hwxi.dats
	$(ATSCC) -o $@ problem25-hwxi.dats -lats -lgmp && ./problem25-hwxi
problem25-hwxi2: problem25-hwxi2.dats
	$(ATSCC) -D_ATS_GCATS -o $@ problem25-hwxi2.dats && ./problem25-hwxi2

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem25-hwxi
	rm -f problem25-hwxi2

###### end of [Makefile] ######
