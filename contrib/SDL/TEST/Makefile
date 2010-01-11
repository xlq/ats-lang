#
#
# Some programs involving SDL
#
#

ATSCC="$(ATSHOME)"/bin/atscc
ATSCTRB="$(ATSHOME)"/contrib/SDL/atsctrb_SDL.o
ATSCTRB_GL="$(ATSHOME)"/contrib/GL/atsctrb_GL.o

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
  lesson13 \
  lesson16 \
  lesson20 \
  lesson36 \

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

lesson13: LazyFoo-lesson13/lesson13.dats
	$(ATSCC) -IATS utils -o lesson13 \
          LazyFoo-lesson13/lesson13.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson16: LazyFoo-lesson16/lesson16.dats
	$(ATSCC) -IATS utils -o lesson16 \
          LazyFoo-lesson16/lesson16.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image

lesson20: LazyFoo-lesson20/lesson20.dats
	$(ATSCC) -IATS utils -o lesson20 \
          LazyFoo-lesson20/lesson20.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image

lesson36: LazyFoo-lesson36/lesson36.dats
	$(ATSCC) -IATS utils -o lesson36 \
          LazyFoo-lesson36/lesson36.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) $(ATSCTRB_GL) -lSDL -lGL

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
	rm -f lesson13
	rm -f lesson16
	rm -f lesson20
	rm -f lesson36

###### end of [Makefile] ######
