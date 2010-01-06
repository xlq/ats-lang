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
  test1 \
  test2 \
  test3-1 test3-2 \
  test4 \
  test5 \
  test6 \
  test7 \
  test8 \
  test9 \
  test10 \

test1: SDL-test1.dats
	$(ATSCC) -o test1 SDL-test1.dats $(ATSCTRB) -lSDL

test2: SDL-test2.dats
	$(ATSCC) -o test2 SDL-test2.dats $(ATSCTRB) -lSDL

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f test1
	rm -f test2

###### end of [Makefile] ######
