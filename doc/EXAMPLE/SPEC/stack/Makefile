#
# A simple make file
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

test:
	$(ATSCC) -o $@ stack_list.sats stack_list.dats test.dats && ./test

######

clean::
	rm -f *~
	rm -f *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; rm -f test

###### end of [Makefile] ######
