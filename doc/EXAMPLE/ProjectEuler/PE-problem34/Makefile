######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem34-hwxi \

######

problem34-hwxi: problem34-hwxi.dats
	$(ATSCC) -O3 -o $@ problem34-hwxi.dats && ./problem34-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem34-hwxi

###### end of [Makefile] ######
