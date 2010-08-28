######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem104-hwxi \

######

problem104-hwxi: problem104-hwxi.dats
	$(ATSCC) -o $@ problem104-hwxi.dats -lgmp && ./problem104-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem104-hwxi

###### end of [Makefile] ######
