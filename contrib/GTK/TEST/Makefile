#
#
#

######

ATSCC=$(ATSHOME)/bin/atscc

######

all:: \
  test01 \
  test02 \
  test03 \
  test04 \
  test05 \
  test06 \

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

###### end of [Makefile] ######