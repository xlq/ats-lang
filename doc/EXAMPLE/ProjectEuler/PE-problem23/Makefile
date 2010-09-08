######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem23-hwxi \

######

problem23-hwxi: problem23-hwxi.dats
	$(ATSCC) -O2 -o $@ problem23-hwxi.dats && ./problem23-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem23-hwxi

###### end of [Makefile] ######
