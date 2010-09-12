######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem48-hwxi \

######

problem48-hwxi: problem48-hwxi.dats
	$(ATSCC) -O2 -o $@ problem48-hwxi.dats -lats -lgmp && ./problem48-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem48-hwxi

###### end of [Makefile] ######
