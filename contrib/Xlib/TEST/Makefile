#
#
# Some programs involving OpenGL
#
#

ATSCC="$(ATSHOME)"/bin/atscc
ATSCTRB="$(ATSHOME)"/contrib/Xlib/atsctrb_Xlib.o

######

checkall: compall cleanall

######

compall: \
  test01 \

test01: Xlib-test01.dats
	$(ATSCC) -o test01 Xlib-test01.dats $(ATSCTRB) -lX11

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f test01

###### end of [Makefile] ######
