######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem9-hwxi \

######

problem9-hwxi: problem9-hwxi.dats
	$(ATSCC) -o $@ problem9-hwxi.dats && ./problem9-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem9-hwxi

###### end of [Makefile] ######
