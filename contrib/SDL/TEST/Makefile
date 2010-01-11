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
  lesson05 \
  lesson06 \
  lesson07 \
  lesson08 \
  lesson09 \
  lesson10 \
  lesson12 \
  lesson20 \

######

lesson01: LazyFoo-lesson01/lesson01.dats
	$(ATSCC) -o lesson01 LazyFoo-lesson01/lesson01.dats $(ATSCTRB) -lSDL

lesson02: LazyFoo-lesson02/lesson02.dats
	$(ATSCC) -o lesson02 LazyFoo-lesson02/lesson02.dats $(ATSCTRB) -lSDL

#
#lesson03: there is no code for lesson03
#

lesson04: LazyFoo-lesson04/lesson04.dats
	$(ATSCC) -o lesson04 LazyFoo-lesson04/lesson04.dats $(ATSCTRB) -lSDL -lSDL_image

lesson05: LazyFoo-lesson05/lesson05.dats
	$(ATSCC) -o lesson05 LazyFoo-lesson05/lesson05.dats $(ATSCTRB) -lSDL -lSDL_image

lesson06: LazyFoo-lesson06/lesson06.dats
	$(ATSCC) -o lesson06 LazyFoo-lesson06/lesson06.dats $(ATSCTRB) -lSDL -lSDL_image

lesson07: LazyFoo-lesson07/lesson07.dats
	$(ATSCC) -o lesson07 LazyFoo-lesson07/lesson07.dats $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson08: LazyFoo-lesson08/lesson08.dats
	$(ATSCC) -o lesson08 LazyFoo-lesson08/lesson08.dats $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson09: LazyFoo-lesson09/lesson09.dats
	$(ATSCC) -o lesson09 LazyFoo-lesson09/lesson09.dats $(ATSCTRB) -lSDL -lSDL_image

lesson10: LazyFoo-lesson10/lesson10.dats
	$(ATSCC) -o lesson10 LazyFoo-lesson10/lesson10.dats $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

#
# lesson11: skipped for now
#

lesson12: LazyFoo-lesson12/lesson12.dats
	$(ATSCC) -o lesson12 LazyFoo-lesson12/lesson12.dats $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson20: \
  LazyFoo-lesson20/lesson20.dats \
  LazyFoo-lesson20/timer.sats LazyFoo-lesson20/timer.dats
	$(ATSCC) -IATS LazyFoo-lesson20 -o lesson20 \
  LazyFoo-lesson20/lesson20.dats \
  LazyFoo-lesson20/timer.sats LazyFoo-lesson20/timer.dats \
  $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f lesson01
	rm -f lesson02
	rm -f lesson04
	rm -f lesson05
	rm -f lesson06
	rm -f lesson07
	rm -f lesson08
	rm -f lesson09
	rm -f lesson10
	rm -f lesson12
	rm -f lesson20

###### end of [Makefile] ######
