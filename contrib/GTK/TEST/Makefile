#
# A simple Makefile for GTK tests
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
GTKFLAGS=`pkg-config gtk+-2.0 --cflags --libs`
ATSGTKLIB=$(ATSHOMEQ)/contrib/GTK/atsctrb_GTK.o

######

.PHONY: all
all:: checkall

######

checkall:: compall cleanall

compall:: \
  test01 \
  test02 \
  test03 \
  test04 \
  test05 \
  test06 \
  test07 \
  test08 \
  test09 \
  test10 \
  test11 \
  test12 \
  test13 \
  test14 \
  test15-1 test15-2 \
  test16 \
  test17 \
  test18 \
  test19 \
  test20 \

######

test01: gtk-test01.dats
	$(ATSCC) -o test01 gtk-test01.dats $(GTKFLAGS)

test02: gtk-test02.dats
	$(ATSCC) -o test02 gtk-test02.dats $(GTKFLAGS)

test03: gtk-test03.dats
	$(ATSCC) -o test03 gtk-test03.dats $(GTKFLAGS)

test04: gtk-test04.dats
	$(ATSCC) -o test04 gtk-test04.dats $(GTKFLAGS)

test05: gtk-test05.dats
	$(ATSCC) -o test05 gtk-test05.dats $(GTKFLAGS)

test06: gtk-test06.dats
	$(ATSCC) -o test06 gtk-test06.dats $(GTKFLAGS)

test07: gtk-test07.dats
	$(ATSCC) -o test07 gtk-test07.dats $(GTKFLAGS)

test08: gtk-test08.dats
	$(ATSCC) -o test08 gtk-test08.dats $(GTKFLAGS)

test09: gtk-test09.dats
	$(ATSCC) -o test09 gtk-test09.dats $(GTKFLAGS)

######

test10: gtk-test10.dats
	$(ATSCC) -o test10 gtk-test10.dats $(GTKFLAGS)

test11: gtk-test11.dats
	$(ATSCC) -o test11 gtk-test11.dats $(GTKFLAGS)

test12: gtk-test12.dats
	$(ATSCC) -o test12 gtk-test12.dats $(GTKFLAGS)

test13: gtk-test13.dats
	$(ATSCC) -o test13 gtk-test13.dats $(GTKFLAGS)

test14: gtk-test14.dats
	$(ATSCC) -o test14 gtk-test14.dats $(GTKFLAGS)

######

test15-1: gtk-test15-1.dats
	$(ATSCC) -o test15-1 gtk-test15-1.dats $(GTKFLAGS)

test15-2: gtk-test15-2.dats
	$(ATSCC) -o test15-2 gtk-test15-2.dats $(GTKFLAGS)

######

test16: gtk-test16.dats
	$(ATSCC) -o test16 gtk-test16.dats $(GTKFLAGS)

test17: gtk-test17.dats
	$(ATSCC) -o test17 gtk-test17.dats $(GTKFLAGS)

test18: gtk-test18.dats
	$(ATSCC) -o test18 gtk-test18.dats $(GTKFLAGS)

test19: gtk-test19.dats
	$(ATSCC) -o test19 gtk-test19.dats $(GTKFLAGS)

######

test20: gtk-test20.dats
	$(ATSCC) -o test20 \
        $(ATSGTKLIB) gtk-test20.dats $(GTKFLAGS)

######

clean::
	rm -f *~
	rm -f *_?ats.c
	rm -f *_?ats.o

cleanall: clean
	rm -f test01
	rm -f test02
	rm -f test03
	rm -f test04
	rm -f test05
	rm -f test06
	rm -f test07
	rm -f test08
	rm -f test09
	rm -f test10
	rm -f test11
	rm -f test12
	rm -f test13
	rm -f test14
	rm -f test15-1 test15-2
	rm -f test16
	rm -f test17
	rm -f test18
	rm -f test19
	rm -f test20

###### end of [Makefile] ######
