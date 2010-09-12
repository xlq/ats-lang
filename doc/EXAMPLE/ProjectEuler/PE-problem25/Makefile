######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem25-hwxi \

######

problem25-hwxi: problem25-hwxi.dats
	$(ATSCC) -o $@ problem25-hwxi.dats -lats -lgmp && ./problem25-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem25-hwxi

###### end of [Makefile] ######
