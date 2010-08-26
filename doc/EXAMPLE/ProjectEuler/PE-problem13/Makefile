######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem13-hwxi \

######

problem13-hwxi: problem13-hwxi.dats
	$(ATSCC) -o $@ problem13-hwxi.dats -lgmp && ./problem13-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem13-hwxi

###### end of [Makefile] ######
