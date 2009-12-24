#
#
# Some programs involving the CAIRO drawing package
#
#


######

ATSCC=$(ATSHOME)/bin/atscc
INCLUDE=-I/usr/include/cairo
OBJFILE=$(ATSHOME)/contrib/cairo/SATS/cairo_sats.o


######

test1: cairo-test1.dats
	$(ATSCC) -o test1 $(INCLUDE) $(OBJFILE) cairo-test1.dats -lcairo \
     && ./test1

test2: cairo-test2.dats
	$(ATSCC) -o test2 $(INCLUDE) $(OBJFILE) cairo-test2.dats -lcairo \
     && ./test2

test3: cairo-test3.dats
	$(ATSCC) -o test3 $(INCLUDE) $(OBJFILE) cairo-test3.dats -lcairo \
     && ./test3

test4: cairo-test4.dats
	$(ATSCC) -o test4 $(INCLUDE) $(OBJFILE) cairo-test4.dats -lcairo \
     && ./test4

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f test1 hello.png
	rm -f test2 rndrect.png
	rm -f test3 regpoly.png
	rm -f test4 koch.png

###### end of [Makefile] ######