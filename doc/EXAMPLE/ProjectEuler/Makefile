######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem1 \
  problem3 \

######

problem1: problem1.dats; $(ATSCC) -o $@ problem1.dats -lgmp && ./problem1
problem3: problem3.dats; $(ATSCC) -o $@ problem3.dats -lgmp && ./problem3

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem1
	rm -f problem3

###### end of [Makefile] ######
