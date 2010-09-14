#
#
# Some programs involving the CAIRO drawing package
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: December, 2010
#
#


######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSCTRB=$(ATSHOMEQ)/contrib/cairo/atsctrb_cairo.o
XRFLAGS=`pkg-config cairo --cflags --libs`
GTKFLAGS=`pkg-config gtk+-2.0 --cflags --libs`

######

.PHONY: all
all: checkall

######

checkall: compall cleanall
compall: \
  test1-1 test1-2 \
  test2 \
  test3 \
  test4 \
  test5 \
  test6 \
  test7-1 test7-2 \
  test8-1 test8-2 test8-3 \
  test9 \
  test10 \
  test11 \
  test12 \
  test13 \
  test14 \
  test15 \
  test16 \

######

test1-1: cairo-test1-1.dats
	$(ATSCC) -o test1-1 `pkg-config cairo --cflags --libs` \
          cairo-test1-1.dats \
     && ./test1-1

test1-2: cairo-test1-2.dats
	$(ATSCC) -o test1-2 `pkg-config gtk+-2.0 --cflags --libs` \
          cairo-test1-2.dats \
     # && ./test1-2

######

test2: cairo-test2.dats
	$(ATSCC) -o test2 $(XRFLAGS) cairo-test2.dats \
     && ./test2

test3: cairo-test3.dats
	$(ATSCC) -o test3 $(XRFLAGS) cairo-test3.dats -lm \
     && ./test3

test4: cairo-test4.dats
	$(ATSCC) -o test4 $(XRFLAGS) cairo-test4.dats -lm \
     && ./test4

test5: cairo-test5.dats
	$(ATSCC) -o test5 $(XRFLAGS) cairo-test5.dats -lm \
     && ./test5

test6: cairo-test6.dats
	$(ATSCC) -o test6 $(XRFLAGS) cairo-test6.dats \
     && ./test6

######

test7-1: cairo-test7-1.dats
	$(ATSCC) -o test7-1 $(XRFLAGS) cairo-test7-1.dats \
     && ./test7-1

test7-2: cairo-test7-2.dats
	$(ATSCC) -o test7-2 `pkg-config --cflags --libs gtk+-2.0` cairo-test7-2.dats

######

test8-1: cairo-test8-1.dats
	$(ATSCC) -o test8-1 $(XRFLAGS) cairo-test8-1.dats -lm \
     && ./test8-1

test8-2: cairo-test8-2.dats
	$(ATSCC) -o test8-2 $(XRFLAGS) cairo-test8-2.dats -lX11 -lm \
     # && ./test8-2

test8-3: cairo-test8-3.dats
	$(ATSCC) -o test8-3 $(GTKFLAGS) cairo-test8-3.dats -lX11 -lm \
     # && ./test8-3

######

test9: cairo-test9.dats
	$(ATSCC) -o test9 $(GTKFLAGS) cairo-test9.dats

######

test10: cairo-test10.dats
	$(ATSCC) -o test10 $(XRFLAGS) cairo-test10.dats \
     && ./test10

######

test11: cairo-test11.dats
	$(ATSCC) -o test11 $(XRFLAGS) cairo-test11.dats \
     && ./test11

######

test12: cairo-test12.dats
	$(ATSCC) -o test12 $(GTKFLAGS) cairo-test12.dats \

######

test13: cairo-test13.dats
	$(ATSCC) -o test13 $(XRFLAGS) cairo-test13.dats \
     && ./test13

test14: cairo-test14.dats
	$(ATSCC) -o test14 $(XRFLAGS) cairo-test14.dats \
     && ./test14

test15: cairo-test15.dats
	$(ATSCC) -o test15 $(XRFLAGS) cairo-test15.dats \
     && ./test15

test16: cairo-test16.dats
	$(ATSCC) -o test16 $(XRFLAGS) cairo-test16.dats \
     && ./test16

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f test1-1 cairo-test1-1.png
	rm -f test1-2
	rm -f test2 cairo-test2.png
	rm -f test3 cairo-test3.png
	rm -f test4 cairo-test4.png
	rm -f test5 cairo-test5.png
	rm -f test6 cairo-test6.png
	rm -f test7-1 cairo-test7-1.png
	rm -f test7-2
	rm -f test8-1 cairo-test8-1.png
	rm -f test8-2 test8-3
	rm -f test9
	rm -f test10 cairo-test10.ps
	rm -f test11 cairo-test11.png
	rm -f test12
	rm -f test13 cairo-test13.png
	rm -f test14 cairo-test14.png
	rm -f test15 cairo-test15.png
	rm -f test16 cairo-test16.png

###### end of [Makefile] ######
