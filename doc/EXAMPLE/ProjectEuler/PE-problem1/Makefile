######
#
# A simple Make file
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem1-hwxi \

######

problem1-hwxi: problem1-hwxi.dats
	$(ATSCC) -o $@ problem1-hwxi.dats -lgmp && ./problem1-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem1-hwxi

###### end of [Makefile] ######
