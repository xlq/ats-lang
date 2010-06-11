#
# A simple Makefile for Clutter tests
#

######

ATSCC=$(ATSHOME)/bin/atscc
CLUTTERFLAGS=`pkg-config clutter-1.0 --cflags --libs`
ATSCLUTTERLIB=$(ATSHOME)/contrib/Clutter/atsctrb_clutter.o

######

.PHONY: all
all:: checkall

######

checkall:: compall cleanall

compall:: \
  test01 \

######

test01: clutter-test01.dats
	$(ATSCC) -o test01 clutter-test01.dats $(CLUTTERFLAGS)

######

clean::
	rm -f *~
	rm -f *_?ats.c
	rm -f *_?ats.o

cleanall: clean
	rm -f test01

###### end of [Makefile] ######
