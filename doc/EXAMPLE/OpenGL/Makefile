#
#
# A simple Makefile for some programs involving OpenGL
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#
#

######

.PHONY: all
all: checkall

######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSCTRB=$(ATSHOMEQ)/contrib/GL/atsctrb_GL.o

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
	$(ATSCC) -D_ATS_GCATS -o glIcosahedron glIcosahedron.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

glClipping: glClipping.dats
	$(ATSCC) -o glClipping glClipping.dats $(ATSCTRB) -lGL -lGLU -lglut

glCubeView: glCubeView.dats
	$(ATSCC) -o glCubeView glCubeView.dats $(ATSCTRB) -lGL -lGLU -lglut

glPlanet: glPlanet.dats
	$(ATSCC) -o glPlanet glPlanet.dats $(ATSCTRB) -lGL -lGLU -lglut

glColoredTriangle: glColoredTriangle.dats
	$(ATSCC) -o glColoredTriangle glColoredTriangle.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

glLitSphere: glLitSphere.dats
	$(ATSCC) -o glLitSphere glLitSphere.dats $(ATSCTRB) -lGL -lglut

glLightMove1: glLightMove1.dats
	$(ATSCC) -o glLightMove1 glLightMove1.dats $(ATSCTRB) -lGL -lGLU -lglut

glLightMove2: glLightMove2.dats
	$(ATSCC) -o glLightMove2 glLightMove2.dats $(ATSCTRB) -lGL -lGLU -lglut

glBlending1: glBlending1.dats
	$(ATSCC) -o glBlending1 glBlending1.dats $(ATSCTRB) -lGL -lGLU -lglut

glBlending2: glBlending2.dats
	$(ATSCC) -o glBlending2 glBlending2.dats $(ATSCTRB) -lGL -lglut

glDisplayList1: glDisplayList1.dats
	$(ATSCC) -o glDisplayList1 glDisplayList1.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

######

#
# A little bit animation for fun
#
glFaces: glFaces.dats
	$(ATSCC) -o glFaces glFaces.dats $(ATSCTRB) -lGL -lglut -lm

######

#
# A simple game of Tetris implemented in ATS
#
glTetrix: glTetrix.dats
	$(ATSCC) -O2 -o glTetrix glTetrix.dats $(ATSCTRB) -lGL -lglut -lm

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *.o
	$(RMF) *_?ats.c

cleanall: clean
	$(RMF) glHello
	$(RMF) glDoubleBuffer
	$(RMF) glIcosahedron
	$(RMF) glClipping
	$(RMF) glCubeView
	$(RMF) glPlanet
	$(RMF) glColoredTriangle
	$(RMF) glLitSphere
	$(RMF) glLightMove1
	$(RMF) glLightMove2
	$(RMF) glBlending1
	$(RMF) glBlending2
	$(RMF) glDisplayList1
	$(RMF) glFaces
	$(RMF) glTetrix

###### end of [Makefile] ######
