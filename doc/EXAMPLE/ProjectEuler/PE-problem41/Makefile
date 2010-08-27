######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem41-hwxi \

######

problem41-hwxi: problem41-hwxi.dats
	$(ATSCC) -o $@ problem41-hwxi.dats && ./problem41-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem41-hwxi

###### end of [Makefile] ######
