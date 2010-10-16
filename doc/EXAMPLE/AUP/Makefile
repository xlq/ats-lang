######
#
# Makefile file for some examples translated from the book:
# Advanced UNIX Programming (2nd edition) by Marc Rochkind
#
######

#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Start Time: Summer, 2009
# Second Time: Fall, 2010
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

compall:: \
  testlock \
  backward \
  backward2 \
  pathnames \
  longls \
  getcwdx \

compall:: \
  test421 \
  test4221 \
  test4222 \
  test423 \
  test435 \
  test47 \
  test48 \

compall:: \
  test52 \
  aupsh1 \
  aupsh2 \
  aupsh3 \
  test5173 \

compall:: \
  test631 \
  test65 \

compall:: \
  test811 \
  test813 \
  test814 \
  test823 \
  test826 \
  test83 \
  test8811 \
  test8812 \

compall:: \
  test911 \
  test917 \
  test923 \
  test972 \

######

testlock: AUP_2_4_3.dats
	$(ATSCC) -o $@ AUP_2_4_3.dats

backward: AUP_2_13.dats
	$(ATSCC) -o $@ AUP_2_13.dats \
     && ./backward "AUP_2_13.dats"

backward2: AUP_2_14.dats
	$(ATSCC) -o $@ AUP_2_14.dats \
     && ./backward2 "AUP_2_14.dats"

pathnames: AUP_3_4.dats
	$(ATSCC) -o $@ AUP_3_4.dats \
     && ./pathnames

longls: AUP_3_5.dats
	$(ATSCC) -o $@ AUP_3_5.dats \
     && ./longls

getcwdx: AUP_3_6_4.dats
	$(ATSCC) -o $@ AUP_3_6_4.dats \
     && ./getcwdx

#######

test421: AUP_4_2_1.dats
	$(ATSCC) -o $@ AUP_4_2_1.dats

test4221: AUP_4_2_2_1.dats
	$(ATSCC) -o $@ AUP_4_2_2_1.dats

test4222: AUP_4_2_2_2.dats
	$(ATSCC) -o $@ AUP_4_2_2_2.dats

test423: AUP_4_2_3.dats
	$(ATSCC) -o $@ AUP_4_2_3.dats

test435: AUP_4_3_5.dats
	$(ATSCC) -o $@ AUP_4_3_5.dats

test47: AUP_4_7.dats
	$(ATSCC) -o $@ AUP_4_7.dats \
     && ./test47

test48: AUP_4_8.dats
	$(ATSCC) -o $@ AUP_4_8.dats -lcurses

#######

test52: AUP_5_2.dats
	$(ATSCC) -o $@ AUP_5_2.dats \
     && ./test52

#######

getargs.o: utils/getargs.c
	$(ATSCC) -Wall -c -o $@ $<

aupsh1: AUP_5_4.dats getargs.o
	$(ATSCC) -o $@ $< getargs.o

aupsh2: AUP_5_6.dats getargs.o
	$(ATSCC) -o $@ $< getargs.o

aupsh3: AUP_5_10.dats getargs.o
	$(ATSCC) -o $@ $< getargs.o

#######

test511: AUP_5_11.dats
	$(ATSCC) -Wall -o $@ AUP_5_11.dats \
     && ./test511

#######

aupnice: AUP_5_15.dats
	$(ATSCC) -Wall -o $@ $<

#######

test5173: AUP_5_17_3.dats
	$(ATSCC) -D_ATS_MULTITHREAD -Wall -o $@ AUP_5_17_3.dats -lpthread \
     && ./test5173

#######

errinfo.o: utils/errinfo.sats utils/errinfo.dats
	$(ATSCC) -IATS utils -I utils -Wall -c -o $@ utils/errinfo.dats

test631: AUP_6_3_1.dats errinfo.o
	$(ATSCC) -I utils -Wall -o $@ $< errinfo.o && ./test631

test65: AUP_6_5.dats errinfo.o
	$(ATSCC) -I utils -Wall -o $@ $< errinfo.o && ./test65

#######

test811: AUP_8_1_1.dats; $(ATSCC) -I utils -Wall -o $@ $< && ./test811

test813: AUP_8_1_3.dats; $(ATSCC) -I utils -Wall -o $@ $<

test814: AUP_8_1_4.dats; $(ATSCC) -I utils -Wall -o $@ $< && ./test814

test823: AUP_8_2_3.dats; $(ATSCC) -I utils -Wall -o $@ $< && ./test823

test826: AUP_8_2_6.dats; $(ATSCC) -I utils -Wall -o $@ $< && ./test826

test83: AUP_8_3.dats; $(ATSCC) -Wall -o $@ $< && ./test83

test8811: AUP_8_8_1_1.dats; $(ATSCC) -Wall -o $@ $< && ./test8811
test8812: AUP_8_8_1_2.dats; $(ATSCC) -Wall -o $@ $< && ./test8812

#######

test911: AUP_9_1_1.dats; $(ATSCC) -Wall -o $@ $<
test917: AUP_9_1_7.dats; $(ATSCC) -Wall -o $@ $<
test923: AUP_9_2_3.dats; $(ATSCC) -Wall -o $@ $< && ./test923
test972: AUP_9_7_2.dats; $(ATSCC) -Wall -o $@ $<

#######

RMF = rm -f

#######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
	$(RMF) MySocket
	$(RMF) errinfo.o
	$(RMF) getargs.o

cleanall:: clean
cleanall::
	$(RMF) testlock
	$(RMF) backward
	$(RMF) backward2
	$(RMF) pathnames
	$(RMF) longls
	$(RMF) getcwdx
cleanall::
	$(RMF) test421
	$(RMF) test4221
	$(RMF) test4222
	$(RMF) test423
	$(RMF) test435
	$(RMF) test47
	$(RMF) test48
cleanall::
	$(RMF) test52
	$(RMF) aupsh1
	$(RMF) aupsh2
	$(RMF) aupsh3
	$(RMF) test511
	$(RMF) aupnice
	$(RMF) test5173
cleanall::
	$(RMF) test631
	$(RMF) test65
cleanall::
	$(RMF) test811
	$(RMF) test813
	$(RMF) test814
	$(RMF) test823
	$(RMF) test826
	$(RMF) test83
	$(RMF) test8811
	$(RMF) test8812
cleanall::
	$(RMF) test911
	$(RMF) test917
	$(RMF) test923
	$(RMF) test972

###### end of [Makefile] ######
