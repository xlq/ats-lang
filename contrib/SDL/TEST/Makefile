#
#
# Some programs involving SDL
#
#

ATSCC="$(ATSHOME)"/bin/atscc
ATSCTRB="$(ATSHOME)"/contrib/SDL/atsctrb_SDL.o

######

checkall: compall cleanall

######

compall: \
  lesson01 \
  lesson02 \
  lesson04 \

######

lesson01: LazyFoo-lesson01/lesson01.dats
	$(ATSCC) -o lesson01 LazyFoo-lesson01/lesson01.dats $(ATSCTRB) -lSDL

lesson02: LazyFoo-lesson02/lesson02.dats
	$(ATSCC) -o lesson02 LazyFoo-lesson02/lesson02.dats $(ATSCTRB) -lSDL

lesson04: LazyFoo-lesson04/lesson04.dats
	$(ATSCC) -o lesson04 LazyFoo-lesson04/lesson04.dats $(ATSCTRB) -lSDL

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f lesson01
	rm -f lesson02
	rm -f lesson04

###### end of [Makefile] ######
