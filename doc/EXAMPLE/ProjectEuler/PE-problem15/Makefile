######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem15-hwxi \

######

problem15-hwxi: problem15-hwxi.dats
	$(ATSCC) -o $@ problem15-hwxi.dats -lgmp && ./problem15-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem15-hwxi

###### end of [Makefile] ######
