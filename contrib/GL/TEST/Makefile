#
#
# Some programs involving OpenGL
#
#

ATSCC="$(ATSHOME)"/bin/atscc
ATSCTRB="$(ATSHOME)"/contrib/GL/atsctrb_GL.o

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

test1: GL-test1.dats
	$(ATSCC) -o test1 GL-test1.dats $(ATSCTRB) -lGL -lglut

test2: GL-test2.dats
	$(ATSCC) -o test2 GL-test2.dats $(ATSCTRB) -lGL -lglut

test3-1: GL-test3-1.dats
	$(ATSCC) -o test3-1 GL-test3-1.dats $(ATSCTRB) -lGL -lglut

test3-2: GL-test3-2.dats
	$(ATSCC) -o test3-2 GL-test3-2.dats $(ATSCTRB) -lGL -lglut

test4: GL-test4.dats
	$(ATSCC) -o test4 GL-test4.dats $(ATSCTRB) -lGL -lglut

test5: GL-test5.dats
	$(ATSCC) -o test5 GL-test5.dats $(ATSCTRB) -lGL -lglut

test6: GL-test6.dats
	$(ATSCC) -O3 -o test6 GL-test6.dats $(ATSCTRB) -lGL -lglut

test7: GL-test7.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o test7 GL-test7.dats $(ATSCTRB) -lGL -lglut

test8: GL-test8.dats
	$(ATSCC) -O3 -o test8 GL-test8.dats $(ATSCTRB) -lGL -lglut

test9: GL-test9.dats
	$(ATSCC) -O3 -o test9 GL-test9.dats $(ATSCTRB) -lGL -lglut

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f test1
	rm -f test2
	rm -f test3-1 test3-2
	rm -f test4
	rm -f test5
	rm -f test6
	rm -f test7
	rm -f test8
	rm -f test9

###### end of [Makefile] ######
