#
#
# Some programs involving Xlib programming
#
#

ATSCC="$(ATSHOME)"/bin/atscc
ATSCTRB="$(ATSHOME)"/contrib/X11/atsctrb_X11.o

######

.PHONY: all
all: checkall

######

checkall: compall cleanall

######

compall: \
  test01 \
  test02 \

######

test01: Xlib-test01.dats
	$(ATSCC) -o test01 Xlib-test01.dats $(ATSCTRB) -lX11

test02: Xlib-test02.dats
	$(ATSCC) -o test02 Xlib-test02.dats $(ATSCTRB) -lX11

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f test01 test02

###### end of [Makefile] ######
