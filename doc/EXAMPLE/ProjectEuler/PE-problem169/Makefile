######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem169-hwxi \

######

problem169-hwxi: problem169-hwxi.dats
	$(ATSCC) -O2 -o $@ problem169-hwxi.dats -lgmp && ./problem169-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem169-hwxi

###### end of [Makefile] ######
