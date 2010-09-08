######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem11-hwxi \

######

problem11-hwxi: problem11-hwxi.dats
	$(ATSCC) -O2 -o $@ problem11-hwxi.dats && ./problem11-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem11-hwxi

###### end of [Makefile] ######
