######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem65-hwxi \

######

problem65-hwxi: problem65-hwxi.dats
	$(ATSCC) -O2 -o $@ problem65-hwxi.dats -lats -lgmp && ./problem65-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem65-hwxi

###### end of [Makefile] ######
