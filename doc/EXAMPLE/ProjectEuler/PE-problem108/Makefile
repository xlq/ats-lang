######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem108-hwxi \

######

problem108-hwxi: problem108-hwxi.dats
	$(ATSCC) -O2 -o $@ problem108-hwxi.dats && ./problem108-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem108-hwxi

###### end of [Makefile] ######
