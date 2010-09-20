######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem94-hwxi \

######

problem94-hwxi: problem94-hwxi.dats
	$(ATSCC) -O3 -o $@ problem94-hwxi.dats -lm && ./problem94-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem94-hwxi

###### end of [Makefile] ######
