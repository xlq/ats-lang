######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem57-hwxi \

######

problem57-hwxi: problem57-hwxi.dats
	$(ATSCC) -O2 -o $@ problem57-hwxi.dats -lgmp && ./problem57-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem57-hwxi

###### end of [Makefile] ######
