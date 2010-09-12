######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem20-hwxi \

######

problem20-hwxi: problem20-hwxi.dats
	$(ATSCC) -o $@ problem20-hwxi.dats -lats -lgmp && ./problem20-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem20-hwxi

###### end of [Makefile] ######
