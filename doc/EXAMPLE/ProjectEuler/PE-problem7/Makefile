######
#
# A simple Make file
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem7-hwxi \

######

problem7-hwxi: problem7-hwxi.dats
	$(ATSCC) -o $@ problem7-hwxi.dats -lgmp && ./problem7-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem7-hwxi

###### end of [Makefile] ######
