#
# A simple make file
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

.PHONY: all
all:: test_list
all:: test_array

######

test_list:
	$(ATSCC) -o $@ stack_list.sats stack_list.dats test_list.dats && ./test_list
test_array:
	$(ATSCC) -o $@ stack_array.sats stack_array.dats test_array.dats && ./test_array

######

clean::
	rm -f *~
	rm -f *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; rm -f test_list
cleanall:: ; rm -f test_array

###### end of [Makefile] ######
