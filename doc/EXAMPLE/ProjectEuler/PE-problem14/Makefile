######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem14-hwxi \

######

problem14-hwxi: problem14-hwxi.dats
	$(ATSCC) -o $@ problem14-hwxi.dats -lgmp && ./problem14-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem14-hwxi

###### end of [Makefile] ######
