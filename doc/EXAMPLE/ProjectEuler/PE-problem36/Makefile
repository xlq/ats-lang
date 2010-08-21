######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem36-hwxi \

######

problem36-hwxi: problem36-hwxi.dats
	$(ATSCC) -O2 -o $@ problem36-hwxi.dats && ./problem36-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem36-hwxi

###### end of [Makefile] ######
