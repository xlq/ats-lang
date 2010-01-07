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

lesson01: LazyFoo-lesson01/lesson01.dats
	$(ATSCC) -o lesson01 LazyFoo-lesson01/lesson01.dats $(ATSCTRB) -lSDL

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f lesson01
	rm -f lesson02

###### end of [Makefile] ######
