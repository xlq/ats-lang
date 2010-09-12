######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem32-hwxi \

######

problem32-hwxi: problem32-hwxi.dats
	$(ATSCC) -O3 -o $@ problem32-hwxi.dats && ./problem32-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem32-hwxi

###### end of [Makefile] ######
