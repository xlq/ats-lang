######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem6-hwxi \

######

problem6-hwxi: problem6-hwxi.dats
	$(ATSCC) -o $@ problem6-hwxi.dats && ./problem6-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem6-hwxi

###### end of [Makefile] ######
