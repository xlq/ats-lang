######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem29-hwxi \

######

problem29-hwxi: problem29-hwxi.dats
	$(ATSCC) -o $@ problem29-hwxi.dats -lgmp && ./problem29-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem29-hwxi

###### end of [Makefile] ######
