######
#
# Makefile file for some examples translated from the book:
# Advanced UNIX Programming (2nd edition) by Marc Rochkind
#
######

#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Start Time: Summer, 2009
#

######

ATSHOMEQ = $(or $(ATSHOME), "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all
all: checkall

######

checkall: compall cleanall

######

compall: \
  testlock \
  backward \
  backward2 \
  pathnames \
  longls \
  getcwdx \
  test421 \
  test4221 \
  test4222 \
  test423 \
  test435 \
  test47 \
  test48 \
  test52 \

######

testlock: AUP_2_4_3.dats
	$(ATSCC) -o testlock AUP_2_4_3.dats

backward: AUP_2_13.dats
	$(ATSCC) -o backward AUP_2_13.dats \
     && ./backward "AUP_2_13.dats"

backward2: AUP_2_14.dats
	$(ATSCC) -o backward2 AUP_2_14.dats \
     && ./backward2 "AUP_2_14.dats"

pathnames: AUP_3_4.dats
	$(ATSCC) -o pathnames AUP_3_4.dats \
     && ./pathnames

longls: AUP_3_5.dats
	$(ATSCC) -o longls AUP_3_5.dats \
     && ./longls

getcwdx: AUP_3_6_4.dats
	$(ATSCC) -o getcwdx AUP_3_6_4.dats \
     && ./getcwdx

#######

test421: AUP_4_2_1.dats
	$(ATSCC) -o test421 AUP_4_2_1.dats

test4221: AUP_4_2_2_1.dats
	$(ATSCC) -o test4221 AUP_4_2_2_1.dats

test4222: AUP_4_2_2_2.dats
	$(ATSCC) -o test4222 AUP_4_2_2_2.dats

test423: AUP_4_2_3.dats
	$(ATSCC) -o test423 AUP_4_2_3.dats

test435: AUP_4_3_5.dats
	$(ATSCC) -o test435 AUP_4_3_5.dats

test47: AUP_4_7.dats
	$(ATSCC) -o test47 AUP_4_7.dats \
     && ./test47

test48: AUP_4_8.dats
	$(ATSCC) -o test48 AUP_4_8.dats -lcurses

#######

test52: AUP_5_2.dats
	$(ATSCC) -o test52 AUP_5_2.dats \
     && ./test52

#######

clean::
	rm -f *~
	rm -f *_?ats.c *_?ats.o

cleanall: clean
	rm -f testlock
	rm -f backward
	rm -f backward2
	rm -f pathnames
	rm -f longls
	rm -f getcwdx
	rm -f test421
	rm -f test4221
	rm -f test4222
	rm -f test423
	rm -f test435
	rm -f test47
	rm -f test48
	rm -f test52

###### end of [Makefile] ######
