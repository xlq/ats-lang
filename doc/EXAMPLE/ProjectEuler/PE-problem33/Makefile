######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem33-hwxi \

######

problem33-hwxi: problem33-hwxi.dats
	$(ATSCC) -o $@ problem33-hwxi.dats && ./problem33-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem33-hwxi

###### end of [Makefile] ######
