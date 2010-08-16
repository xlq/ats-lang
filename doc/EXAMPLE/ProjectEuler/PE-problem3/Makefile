######
#
# A simple Make file
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem3-hwxi \

######

problem3-hwxi: problem3-hwxi.dats
	$(ATSCC) -o $@ problem3-hwxi.dats -lgmp && ./problem3-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem3-hwxi

###### end of [Makefile] ######
