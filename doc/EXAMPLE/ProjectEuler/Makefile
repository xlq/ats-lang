######

ATSCC=$(ATSHOME)/bin/atscc

######

problem3: problem3.dats; $(ATSCC) -o $@ problem3.dats -lgmp && ./problem3

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem3

###### end of [Makefile] ######
