######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem92-hwxi \

######

problem92-hwxi: problem92-hwxi.dats
	$(ATSCC) -O3 -o $@ problem92-hwxi.dats -lgmp && ./problem92-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem92-hwxi

###### end of [Makefile] ######
