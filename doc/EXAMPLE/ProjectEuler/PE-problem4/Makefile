######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem4-hwxi \

######

problem4-hwxi: problem4-hwxi.dats
	$(ATSCC) -o $@ problem4-hwxi.dats && ./problem4-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem4-hwxi

###### end of [Makefile] ######
