######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem56-hwxi \

######

problem56-hwxi: problem56-hwxi.dats
	$(ATSCC) -O2 -o $@ problem56-hwxi.dats -lgmp && ./problem56-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem56-hwxi

###### end of [Makefile] ######
