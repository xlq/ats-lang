######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem164-hwxi \

######

problem164-hwxi: problem164-hwxi.dats
	$(ATSCC) -O2 -o $@ problem164-hwxi.dats && ./problem164-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem164-hwxi

###### end of [Makefile] ######
