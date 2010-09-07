######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem43-hwxi \

######

problem43-hwxi: problem43-hwxi.dats
	$(ATSCC) -o $@ problem43-hwxi.dats && ./problem43-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem43-hwxi

###### end of [Makefile] ######
