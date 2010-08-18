######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem63-hwxi \

######

problem63-hwxi: problem63-hwxi.dats
	$(ATSCC) -O2 -o $@ problem63-hwxi.dats -lm && ./problem63-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem63-hwxi

###### end of [Makefile] ######
