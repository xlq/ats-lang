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

checkall: \
  test1 test2 test3 test4 test5 test6 test7 test8 test9 \
  test10 test11 test12 test13 test14 test15 \
  cleanall

######

test1: cairo-test1.dats
	$(ATSCC) -o test1 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test1.dats \
     && ./test1

test2: cairo-test2.dats
	$(ATSCC) -o test2 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test2.dats \
     && ./test2

test3: cairo-test3.dats
	$(ATSCC) -o test3 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test3.dats \
     && ./test3

test4: cairo-test4.dats
	$(ATSCC) -o test4 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test4.dats \
     && ./test4

test5: cairo-test5.dats
	$(ATSCC) -o test5 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test5.dats \
     && ./test5

test6: cairo-test6.dats
	$(ATSCC) -o test6 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test6.dats \
     && ./test6

test7: cairo-test7.dats
	$(ATSCC) -o test7 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test7.dats \
     && ./test7

test8: cairo-test8.dats
	$(ATSCC) -o test8 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test8.dats \
     && ./test8

test9: cairo-test9.dats
	$(ATSCC) -o test9 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test9.dats -lX11

test10: cairo-test10.dats
	$(ATSCC) -o test10 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test10.dats \
     && ./test10

test11: cairo-test11.dats
	$(ATSCC) -o test11 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test11.dats \
     && ./test11

test12: cairo-test12.dats
	$(ATSCC) -o test12 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test12.dats \
     && ./test12

test13: cairo-test13.dats
	$(ATSCC) -o test13 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test13.dats \
     && ./test13

test14: cairo-test14.dats
	$(ATSCC) -o test14 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test14.dats \
     && ./test14

test15: cairo-test15.dats
	$(ATSCC) -o test15 `pkg-config --cflags --libs cairo` $(ATSCTRB) \
          cairo-test15.dats \
     && ./test15

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f test1 cairo-test1.png
	rm -f test2 cairo-test2.png
	rm -f test3 cairo-test3.png
	rm -f test4 cairo-test4.png
	rm -f test5 cairo-test5.png
	rm -f test6 cairo-test6.png
	rm -f test7 cairo-test7.png
	rm -f test8 cairo-test8.png
	rm -f test9 cairo-test9.png
	rm -f test10 cairo-test10.ps
	rm -f test11 cairo-test11.png
	rm -f test12 cairo-test12.png
	rm -f test13 cairo-test13.png
	rm -f test14 cairo-test14.png
	rm -f test15 cairo-test15.png

###### end of [Makefile] ######