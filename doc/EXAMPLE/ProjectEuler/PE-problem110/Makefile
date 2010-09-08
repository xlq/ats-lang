######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem110-hwxi \

######

problem110-hwxi: problem110-hwxi.dats
	$(ATSCC) -O2 -o $@ problem110-hwxi.dats -lm && ./problem110-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem110-hwxi

###### end of [Makefile] ######
