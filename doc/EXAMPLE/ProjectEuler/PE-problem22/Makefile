######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem22-hwxi \

######

problem22-hwxi: problem22-hwxi.dats
	$(ATSCC) -o $@ problem22-hwxi.dats && ./problem22-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem22-hwxi

###### end of [Makefile] ######
