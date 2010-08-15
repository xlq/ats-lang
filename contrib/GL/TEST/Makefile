#
#
# Some programs involving OpenGL
#
#

ATSCC="$(ATSHOME)"/bin/atscc
ATSCTRB="$(ATSHOME)"/contrib/GL/atsctrb_GL.o

######

.PHONY:: checkall
checkall:: compall cleanall

######

compall:: \
  test01 \
  test02 \
  test03-1 test03-2 \
  test04 \
  test05 \
  test06 \
  test07 \
  test08 \
  test09 \
  test10 \
  test11 \
  test12 \
  test13 \
  test14 \
  test15 \

test01: GL-test01.dats
	$(ATSCC) -o test01 GL-test01.dats $(ATSCTRB) -lGL -lGLU -lglut

test02: GL-test02.dats
	$(ATSCC) -o test02 GL-test02.dats $(ATSCTRB) -lGL -lGLU -lglut

test03-1: GL-test03-1.dats
	$(ATSCC) -o test03-1 GL-test03-1.dats $(ATSCTRB) -lGL -lGLU -lglut

test03-2: GL-test03-2.dats
	$(ATSCC) -o test03-2 GL-test03-2.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

test04: GL-test04.dats
	$(ATSCC) -o test04 GL-test04.dats $(ATSCTRB) -lGL -lGLU -lglut

test05: GL-test05.dats
	$(ATSCC) -o test05 GL-test05.dats $(ATSCTRB) -lGL -lGLU -lglut

test06: GL-test06.dats
	$(ATSCC) -O3 -o test06 GL-test06.dats $(ATSCTRB) -lGL -lGLU -lglut

test07: GL-test07.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o test07 GL-test07.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

test08: GL-test08.dats
	$(ATSCC) -O3 -o test08 GL-test08.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

test09: GL-test09.dats
	$(ATSCC) -O3 -o test09 GL-test09.dats $(ATSCTRB) -lGL -lGLU -lglut

######

test10: GL-test10.dats
	$(ATSCC) -O3 -o test10 GL-test10.dats $(ATSCTRB) -lGL -lGLU -lglut

test11: GL-test11.dats
	$(ATSCC) -O3 -o test11 GL-test11.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

test12: GL-test12.dats
	$(ATSCC) -g -o test12 GL-test12.dats $(ATSCTRB) -lGL -lGLU -lglut

test13: GL-test13.dats
	$(ATSCC) -g -o test13 GL-test13.dats $(ATSCTRB) -lGL -lGLU -lglut

test14: GL-test14.dats
	$(ATSCC) -g -o test14 GL-test14.dats $(ATSCTRB) -lGL -lGLU -lglut

test15: GL-test15.dats
	$(ATSCC) -g -o test15 GL-test15.dats $(ATSCTRB) -lGL -lGLU -lglut

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f test01
	rm -f test02
	rm -f test03-1 test03-2
	rm -f test04
	rm -f test05
	rm -f test06
	rm -f test07
	rm -f test08
	rm -f test09
	rm -f test10
	rm -f test11
	rm -f test12
	rm -f test13
	rm -f test14
	rm -f test15

###### end of [Makefile] ######
