######
#
# Makefile file for some examples translated from the book:
# Advanced UNIX Programming (2nd edition) by Marc Rochkind
#
######

#
# Time: Summer, 2009
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#

######

ATSCC=$(ATSHOME)/bin/atscc

######

checkall: compall cleanall

######

compall: \
  testlock \
  backward2 \
  getcwdx \

######

testlock: AUP_2_4_3.dats
	$(ATSCC) -o testlock AUP_2_4_3.dats

backward2: AUP_2_14_0.dats
	$(ATSCC) -o backward2 AUP_2_14_0.dats \
     && ./backward2 "AUP_2_14_0.dats"

getcwdx: AUP_3_6_4.dats
	$(ATSCC) -o getcwdx AUP_3_6_4.dats \
     && ./getcwdx

######

clean::
	rm -f a.out
	rm -f *_?ats.c *_?ats.o
	rm -f *~

cleanall: clean
	rm -f testlock
	rm -f backward2
	rm -f getcwdx

###### end of [Makefile] ######
 