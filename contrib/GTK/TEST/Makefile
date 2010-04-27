#
#
#

######

ATSCC=$(ATSHOME)/bin/atscc

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
  test15 \
  test16 \
  test17 \

######

test01: gtk-test01.dats
	$(ATSCC) -o test01 gtk-test01.dats `pkg-config --cflags --libs gtk+-2.0`

test02: gtk-test02.dats
	$(ATSCC) -o test02 gtk-test02.dats `pkg-config --cflags --libs gtk+-2.0`

test03: gtk-test03.dats
	$(ATSCC) -o test03 gtk-test03.dats `pkg-config --cflags --libs gtk+-2.0`

test04: gtk-test04.dats
	$(ATSCC) -o test04 gtk-test04.dats `pkg-config --cflags --libs gtk+-2.0`

test05: gtk-test05.dats
	$(ATSCC) -o test05 gtk-test05.dats `pkg-config --cflags --libs gtk+-2.0`

test06: gtk-test06.dats
	$(ATSCC) -o test06 gtk-test06.dats `pkg-config --cflags --libs gtk+-2.0`

test07: gtk-test07.dats
	$(ATSCC) -o test07 gtk-test07.dats `pkg-config --cflags --libs gtk+-2.0`

test08: gtk-test08.dats
	$(ATSCC) -o test08 gtk-test08.dats `pkg-config --cflags --libs gtk+-2.0`

test09: gtk-test09.dats
	$(ATSCC) -o test09 gtk-test09.dats `pkg-config --cflags --libs gtk+-2.0`

######

test10: gtk-test10.dats
	$(ATSCC) -o test10 gtk-test10.dats `pkg-config --cflags --libs gtk+-2.0`

test11: gtk-test11.dats
	$(ATSCC) -o test11 gtk-test11.dats `pkg-config --cflags --libs gtk+-2.0`

test12: gtk-test12.dats
	$(ATSCC) -o test12 gtk-test12.dats `pkg-config --cflags --libs gtk+-2.0`

test13: gtk-test13.dats
	$(ATSCC) -o test13 gtk-test13.dats `pkg-config --cflags --libs gtk+-2.0`

test14: gtk-test14.dats
	$(ATSCC) -o test14 gtk-test14.dats `pkg-config --cflags --libs gtk+-2.0`

test15: gtk-test15.dats
	$(ATSCC) -o test15 gtk-test15.dats `pkg-config --cflags --libs gtk+-2.0`

test16: gtk-test16.dats
	$(ATSCC) -o test16 gtk-test16.dats `pkg-config --cflags --libs gtk+-2.0`

test17: gtk-test17.dats
	$(ATSCC) -o test17 gtk-test17.dats `pkg-config --cflags --libs gtk+-2.0`

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
	rm -f test15
	rm -f test16
	rm -f test17

###### end of [Makefile] ######
