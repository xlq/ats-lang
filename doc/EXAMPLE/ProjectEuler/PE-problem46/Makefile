######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem46-hwxi \

######

problem46-hwxi: problem46-hwxi.dats
	$(ATSCC) -O2 -o $@ problem46-hwxi.dats && ./problem46-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem46-hwxi

###### end of [Makefile] ######
