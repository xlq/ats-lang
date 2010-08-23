######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem157-hwxi \

######

problem157-hwxi: problem157-hwxi.dats
	$(ATSCC) -O2 -o $@ problem157-hwxi.dats && ./problem157-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem157-hwxi

###### end of [Makefile] ######
