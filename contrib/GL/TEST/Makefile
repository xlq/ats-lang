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
  test3 \
  test4 \
  test5 \
  test6 \
  test7 \

test1: GL-test1.dats
	$(ATSCC) -o test1 GL-test1.dats $(ATSCTRB) -lGL -lglut

test2: GL-test2.dats
	$(ATSCC) -o test2 GL-test2.dats $(ATSCTRB) -lGL -lglut

test3: GL-test3.dats
	$(ATSCC) -o test3 GL-test3.dats $(ATSCTRB) -lGL -lglut

test4: GL-test4.dats
	$(ATSCC) -o test4 GL-test4.dats $(ATSCTRB) -lGL -lglut

test5: GL-test5.dats
	$(ATSCC) -o test5 GL-test5.dats $(ATSCTRB) -lGL -lglut

test6: GL-test6.dats
	$(ATSCC) -O3 -o test6 GL-test6.dats $(ATSCTRB) -lGL -lglut

test7: GL-test7.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o test7 GL-test7.dats $(ATSCTRB) -lGL -lglut

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f test1
	rm -f test2
	rm -f test3
	rm -f test4
	rm -f test5
	rm -f test6
	rm -f test7

###### end of [Makefile] ######
