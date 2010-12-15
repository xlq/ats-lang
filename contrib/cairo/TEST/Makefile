#
#
# Some programs involving the CAIRO drawing package
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: December, 2009
#
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
ATSCTRB=$(ATSLIBQ)/contrib/cairo/atsctrb_cairo.o
XRFLAGS=`pkg-config cairo --cflags --libs`
GTKFLAGS=`pkg-config gtk+-2.0 --cflags --libs`

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean


######

checkall:: test1-1
cleanall:: test1-1
test1-1: cairo-test1-1.dats
	$(ATSCC) -o test1-1 `pkg-config cairo --cflags --libs` \
          cairo-test1-1.dats \
     && ./test1-1

checkall:: test1-2
cleanall:: test1-2
test1-2: cairo-test1-2.dats
	$(ATSCC) -o test1-2 `pkg-config gtk+-2.0 --cflags --libs` \
          cairo-test1-2.dats \
     # && ./test1-2

######

checkall:: test2
cleanall:: test2
test2: cairo-test2.dats
	$(ATSCC) -o test2 $(XRFLAGS) cairo-test2.dats \
     && ./test2

checkall:: test3
cleanall:: test3
test3: cairo-test3.dats
	$(ATSCC) -o test3 $(XRFLAGS) cairo-test3.dats -lm \
     && ./test3

checkall:: test4
cleanall:: test4
test4: cairo-test4.dats
	$(ATSCC) -o test4 $(XRFLAGS) cairo-test4.dats -lm \
     && ./test4

checkall:: test5
cleanall:: test5
test5: cairo-test5.dats
	$(ATSCC) -o test5 $(XRFLAGS) cairo-test5.dats -lm \
     && ./test5

checkall:: test6
cleanall:: test6
test6: cairo-test6.dats
	$(ATSCC) -o test6 $(XRFLAGS) cairo-test6.dats \
     && ./test6

######

checkall:: test7-1
cleanall:: test7-1
test7-1: cairo-test7-1.dats
	$(ATSCC) -o test7-1 $(XRFLAGS) cairo-test7-1.dats \
     && ./test7-1

checkall:: test7-2
cleanall:: test7-2
test7-2: cairo-test7-2.dats
	$(ATSCC) -o test7-2 `pkg-config --cflags --libs gtk+-2.0` cairo-test7-2.dats

######

checkall:: test8-1
cleanall:: test8-1
test8-1: cairo-test8-1.dats
	$(ATSCC) -o test8-1 $(XRFLAGS) cairo-test8-1.dats -lm \
     && ./test8-1

checkall:: test8-2
cleanall:: test8-2
test8-2: cairo-test8-2.dats
	$(ATSCC) -o test8-2 $(XRFLAGS) cairo-test8-2.dats -lX11 -lm \
     # && ./test8-2

checkall:: test8-3
cleanall:: test8-3
test8-3: cairo-test8-3.dats
	$(ATSCC) -o test8-3 $(GTKFLAGS) cairo-test8-3.dats -lX11 -lm \
     # && ./test8-3

######

checkall:: test9
cleanall:: test9
test9: cairo-test9.dats
	$(ATSCC) -o test9 $(GTKFLAGS) cairo-test9.dats

######

checkall:: test10
cleanall:: test10
test10: cairo-test10.dats
	$(ATSCC) -o test10 $(XRFLAGS) cairo-test10.dats \
     && ./test10

######

checkall:: test11
cleanall:: test11
test11: cairo-test11.dats
	$(ATSCC) -o test11 $(XRFLAGS) cairo-test11.dats \
     && ./test11

######

checkall:: test12
cleanall:: test12
test12: cairo-test12.dats
	$(ATSCC) -o test12 $(GTKFLAGS) cairo-test12.dats \

######

checkall:: test13
cleanall:: test13
test13: cairo-test13.dats
	$(ATSCC) -o test13 $(XRFLAGS) cairo-test13.dats \
     && ./test13

checkall:: test14
cleanall:: test14
test14: cairo-test14.dats
	$(ATSCC) -o test14 $(XRFLAGS) cairo-test14.dats \
     && ./test14

checkall:: test15
cleanall:: test15
test15: cairo-test15.dats
	$(ATSCC) -o test15 $(XRFLAGS) cairo-test15.dats \
     && ./test15

checkall:: test16
cleanall:: test16
test16: cairo-test16.dats
	$(ATSCC) -o test16 $(XRFLAGS) cairo-test16.dats \
     && ./test16

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall: clean
	$(RMF) test1-1 cairo-test1-1.png
	$(RMF) test1-2
	$(RMF) test2 cairo-test2.png
	$(RMF) test3 cairo-test3.png
	$(RMF) test4 cairo-test4.png
	$(RMF) test5 cairo-test5.png
	$(RMF) test6 cairo-test6.png
	$(RMF) test7-1 cairo-test7-1.png
	$(RMF) test7-2
	$(RMF) test8-1 cairo-test8-1.png
	$(RMF) test8-2 test8-3
	$(RMF) test9
	$(RMF) test10 cairo-test10.ps
	$(RMF) test11 cairo-test11.png
	$(RMF) test12
	$(RMF) test13 cairo-test13.png
	$(RMF) test14 cairo-test14.png
	$(RMF) test15 cairo-test15.png
	$(RMF) test16 cairo-test16.png

###### end of [Makefile] ######
