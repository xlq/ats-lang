######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem145-hwxi \

######

problem145-hwxi: problem145-hwxi.dats
	$(ATSCC) -O2 -o $@ problem145-hwxi.dats && ./problem145-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem145-hwxi

###### end of [Makefile] ######
