ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

test:
	$(ATSCC) -o $@ stack.sats stack.dats test.dats && ./test

clean::
	rm -f *~
	rm -f *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; rm -f test
