#
#
# Some programs involving OpenGL
#
#

.PHONY: all
all:  compall

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc
ATSCTRB=$(ATSHOME)/contrib/GL/atsctrb_GL.o

######

checkall: compall cleanall

######

compall: \
  glHello \
  glDoubleBuffer \
  glIcosahedron \
  glClipping \
  glCubeView \
  glPlanet \
  glColoredTriangle \
  glLitSphere \
  glLightMove1 \
  glLightMove2 \
  glDisplayList1 \
  glBlending1 \
  glBlending2 \
  glFaces \
  glTetrix \

glHello: glHello.dats
	$(ATSCC) -o glHello glHello.dats $(ATSCTRB) -lGL -lglut

glDoubleBuffer: glDoubleBuffer.dats
	$(ATSCC) -o glDoubleBuffer glDoubleBuffer.dats $(ATSCTRB) -lGL -lglut

glIcosahedron: glIcosahedron.dats
	$(ATSCC) -D_ATS_GCATS -o glIcosahedron glIcosahedron.dats $(ATSCTRB) -lGL -lglut -lm

glClipping: glClipping.dats
	$(ATSCC) -o glClipping glClipping.dats $(ATSCTRB) -lGL -lglut

glCubeView: glCubeView.dats
	$(ATSCC) -o glCubeView glCubeView.dats $(ATSCTRB) -lGL -lglut

glPlanet: glPlanet.dats
	$(ATSCC) -o glPlanet glPlanet.dats $(ATSCTRB) -lGL -lglut

glColoredTriangle: glColoredTriangle.dats
	$(ATSCC) -o glColoredTriangle glColoredTriangle.dats $(ATSCTRB) -lGL -lglut -lm

glLitSphere: glLitSphere.dats
	$(ATSCC) -o glLitSphere glLitSphere.dats $(ATSCTRB) -lGL -lglut

glLightMove1: glLightMove1.dats
	$(ATSCC) -o glLightMove1 glLightMove1.dats $(ATSCTRB) -lGL -lglut

glLightMove2: glLightMove2.dats
	$(ATSCC) -o glLightMove2 glLightMove2.dats $(ATSCTRB) -lGL -lglut

glBlending1: glBlending1.dats
	$(ATSCC) -o glBlending1 glBlending1.dats $(ATSCTRB) -lGL -lglut

glBlending2: glBlending2.dats
	$(ATSCC) -o glBlending2 glBlending2.dats $(ATSCTRB) -lGL -lglut

glDisplayList1: glDisplayList1.dats
	$(ATSCC) -o glDisplayList1 glDisplayList1.dats $(ATSCTRB) -lGL -lglut -lm

#
# A little bit animation for fun
#
glFaces: glFaces.dats
	$(ATSCC) -o glFaces glFaces.dats $(ATSCTRB) -lGL -lglut -lm

#
# A simple game of Tetris implemented in ATS
#
glTetrix: glTetrix.dats
	$(ATSCC) -O2 -o glTetrix glTetrix.dats $(ATSCTRB) -lGL -lglut -lm

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f glHello
	rm -f glDoubleBuffer
	rm -f glIcosahedron
	rm -f glClipping
	rm -f glCubeView
	rm -f glPlanet
	rm -f glColoredTriangle
	rm -f glLitSphere
	rm -f glLightMove1
	rm -f glLightMove2
	rm -f glBlending1
	rm -f glBlending2
	rm -f glDisplayList1
	rm -f glFaces
	rm -f glTetrix

###### end of [Makefile] ######
