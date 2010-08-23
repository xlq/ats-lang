######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem40-hwxi \

######

problem40-hwxi: problem40-hwxi.dats
	$(ATSCC) -o $@ problem40-hwxi.dats && ./problem40-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem40-hwxi

###### end of [Makefile] ######
