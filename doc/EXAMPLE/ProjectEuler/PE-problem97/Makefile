######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem97-hwxi \

######

problem97-hwxi: problem97-hwxi.dats
	$(ATSCC) -o $@ problem97-hwxi.dats -lgmp && ./problem97-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem97-hwxi

###### end of [Makefile] ######
