######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem58-hwxi \

######

problem58-hwxi: problem58-hwxi.dats
	$(ATSCC) -O2 -o $@ problem58-hwxi.dats -lm && ./problem58-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem58-hwxi

###### end of [Makefile] ######
