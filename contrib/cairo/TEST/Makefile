#
#
# Some programs involving the CAIRO drawing package
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: December, 2010
#
#


######

ATSCC=$(ATSHOME)/bin/atscc
ATSCTRB=$(ATSHOME)/contrib/cairo/atsctrb_cairo.o

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

######

test1-1: cairo-test1-1.dats
	$(ATSCC) -o test1-1 `pkg-config --cflags --libs cairo` \
          cairo-test1-1.dats \
     && ./test1-1

test1-2: cairo-test1-2.dats
	$(ATSCC) -o test1-2 `pkg-config --cflags --libs gtk+-2.0` \
          cairo-test1-2.dats \
     # && ./test1-2

######

test2: cairo-test2.dats
	$(ATSCC) -o test2 `pkg-config --cflags --libs cairo` cairo-test2.dats \
     && ./test2

test3: cairo-test3.dats
	$(ATSCC) -o test3 `pkg-config --cflags --libs cairo` cairo-test3.dats \
     && ./test3

test4: cairo-test4.dats
	$(ATSCC) -o test4 `pkg-config --cflags --libs cairo` cairo-test4.dats \
     && ./test4

test5: cairo-test5.dats
	$(ATSCC) -o test5 `pkg-config --cflags --libs cairo` cairo-test5.dats \
     && ./test5

test6: cairo-test6.dats
	$(ATSCC) -o test6 `pkg-config --cflags --libs cairo` cairo-test6.dats \
     && ./test6

######

test7-1: cairo-test7-1.dats
	$(ATSCC) -o test7-1 `pkg-config --cflags --libs cairo` cairo-test7-1.dats \
     && ./test7-1

test7-2: cairo-test7-2.dats
	$(ATSCC) -o test7-2 `pkg-config --cflags --libs gtk+-2.0` cairo-test7-2.dats

######

test8-1: cairo-test8-1.dats
	$(ATSCC) -o test8-1 `pkg-config --cflags --libs cairo` cairo-test8-1.dats \
     && ./test8-1

test8-2: cairo-test8-2.dats
	$(ATSCC) -o test8-2 `pkg-config --cflags --libs cairo` cairo-test8-2.dats -lX11 \
     # && ./test8-2

test8-3: cairo-test8-3.dats
	$(ATSCC) -o test8-3 `pkg-config --cflags --libs gtk+-2.0` cairo-test8-3.dats -lX11 \
     # && ./test8-3

######

test9: cairo-test9.dats
	$(ATSCC) -o test9 `pkg-config --cflags --libs gtk+-2.0` cairo-test9.dats

######

test10: cairo-test10.dats
	$(ATSCC) -o test10 `pkg-config --cflags --libs cairo` cairo-test10.dats \
     && ./test10

test11: cairo-test11.dats
	$(ATSCC) -o test11 `pkg-config --cflags --libs cairo` cairo-test11.dats \
     && ./test11

test12: cairo-test12.dats
	$(ATSCC) -o test12 `pkg-config --cflags --libs cairo` cairo-test12.dats \
     && ./test12

test13: cairo-test13.dats
	$(ATSCC) -o test13 `pkg-config --cflags --libs cairo` cairo-test13.dats \
     && ./test13

test14: cairo-test14.dats
	$(ATSCC) -o test14 `pkg-config --cflags --libs cairo` cairo-test14.dats \
     && ./test14

test15: cairo-test15.dats
	$(ATSCC) -o test15 `pkg-config --cflags --libs cairo` cairo-test15.dats \
     && ./test15

test16: cairo-test16.dats
	$(ATSCC) -o test16 `pkg-config --cflags --libs cairo` cairo-test16.dats \
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
	rm -f test12 cairo-test12.png
	rm -f test13 cairo-test13.png
	rm -f test14 cairo-test14.png
	rm -f test15 cairo-test15.png
	rm -f test16 cairo-test16.png

###### end of [Makefile] ######