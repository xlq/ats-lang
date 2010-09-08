######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem18-hwxi \

######

problem18-hwxi: problem18-hwxi.dats
	$(ATSCC) -o $@ problem18-hwxi.dats && ./problem18-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem18-hwxi

###### end of [Makefile] ######
