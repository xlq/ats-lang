######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem162-hwxi \

######

problem162-hwxi: problem162-hwxi.dats
	$(ATSCC) -O2 -o $@ problem162-hwxi.dats -lats -lgmp && ./problem162-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem162-hwxi

###### end of [Makefile] ######
