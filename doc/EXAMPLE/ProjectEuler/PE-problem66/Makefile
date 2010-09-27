######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem66-hwxi \

######

problem66-hwxi: problem66-hwxi.dats
	$(ATSCC) -O2 -o $@ problem66-hwxi.dats -lats -lgmp -lm && ./problem66-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem66-hwxi

###### end of [Makefile] ######
