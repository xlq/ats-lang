#
# A simple Makefile for GTK tests
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.3"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
GTKFLAGS=`pkg-config gtk+-2.0 --cflags --libs`
ATSGTKLIB=$(ATSLIBQ)/contrib/GTK/atsctrb_GTK.o

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: test01
cleanall:: ; $(RMF) test01
test01: gtk-test01.dats
	$(ATSCC) -o test01 gtk-test01.dats $(GTKFLAGS)

checkall:: test02
cleanall:: ; $(RMF) test02
test02: gtk-test02.dats
	$(ATSCC) -o test02 gtk-test02.dats $(GTKFLAGS)

checkall:: test03
cleanall:: ; $(RMF) test03
test03: gtk-test03.dats
	$(ATSCC) -o test03 gtk-test03.dats $(GTKFLAGS)

checkall:: test04
cleanall:: ; $(RMF) test04
test04: gtk-test04.dats
	$(ATSCC) -o test04 gtk-test04.dats $(GTKFLAGS)

checkall:: test05
cleanall:: ; $(RMF) test05
test05: gtk-test05.dats
	$(ATSCC) -o test05 gtk-test05.dats $(GTKFLAGS)

checkall:: test06
cleanall:: ; $(RMF) test06
test06: gtk-test06.dats
	$(ATSCC) -o test06 gtk-test06.dats $(GTKFLAGS)

checkall:: test07
cleanall:: ; $(RMF) test07
test07: gtk-test07.dats
	$(ATSCC) -o test07 gtk-test07.dats $(GTKFLAGS)

checkall:: test08
cleanall:: ; $(RMF) test08
test08: gtk-test08.dats
	$(ATSCC) -o test08 gtk-test08.dats $(GTKFLAGS)

checkall:: test09
cleanall:: ; $(RMF) test09
test09: gtk-test09.dats
	$(ATSCC) -o test09 gtk-test09.dats $(GTKFLAGS)

######

checkall:: test10
cleanall:: ; $(RMF) test10
test10: gtk-test10.dats
	$(ATSCC) -o test10 gtk-test10.dats $(GTKFLAGS)

checkall:: test11
cleanall:: ; $(RMF) test11
test11: gtk-test11.dats
	$(ATSCC) -o test11 gtk-test11.dats $(GTKFLAGS)

checkall:: test12
cleanall:: ; $(RMF) test12
test12: gtk-test12.dats
	$(ATSCC) -o test12 gtk-test12.dats $(GTKFLAGS)

checkall:: test13
cleanall:: ; $(RMF) test13
test13: gtk-test13.dats
	$(ATSCC) -o test13 gtk-test13.dats $(GTKFLAGS)

checkall:: test14
cleanall:: ; $(RMF) test14
test14: gtk-test14.dats
	$(ATSCC) -o test14 gtk-test14.dats $(GTKFLAGS)

######

checkall:: test15-1
cleanall:: ; $(RMF) test15-1
test15-1: gtk-test15-1.dats
	$(ATSCC) -o test15-1 gtk-test15-1.dats $(GTKFLAGS)

checkall:: test15-2
cleanall:: ; $(RMF) test15-2
test15-2: gtk-test15-2.dats
	$(ATSCC) -o test15-2 gtk-test15-2.dats $(GTKFLAGS)

######

checkall:: test16
cleanall:: ; $(RMF) test16
test16: gtk-test16.dats
	$(ATSCC) -o test16 gtk-test16.dats $(GTKFLAGS)

checkall:: test17
cleanall:: ; $(RMF) test17
test17: gtk-test17.dats
	$(ATSCC) -o test17 gtk-test17.dats $(GTKFLAGS)

checkall:: test18
cleanall:: ; $(RMF) test18
test18: gtk-test18.dats
	$(ATSCC) -o test18 gtk-test18.dats $(GTKFLAGS)

checkall:: test19
cleanall:: ; $(RMF) test19
test19: gtk-test19.dats
	$(ATSCC) -o test19 gtk-test19.dats $(GTKFLAGS)

######

checkall:: test20
cleanall:: ; $(RMF) test20
test20: gtk-test20.dats
	$(ATSCC) -o test20 $(ATSGTKLIB) gtk-test20.dats $(GTKFLAGS)

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c
	$(RMF) *_?ats.o

###### end of [Makefile] ######
