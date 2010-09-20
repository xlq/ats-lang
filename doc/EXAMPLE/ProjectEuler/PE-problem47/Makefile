######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem47-hwxi \

######

problem47-hwxi: problem47-hwxi.dats
	$(ATSCC) -O2 -o $@ problem47-hwxi.dats && ./problem47-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem47-hwxi

###### end of [Makefile] ######
