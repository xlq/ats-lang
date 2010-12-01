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

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSCTRB=$(ATSHOMEQ)/contrib/GL/atsctrb_GL.o

######

checkall: compall cleanall

######

compall:: glHello
glHello: glHello.dats
	$(ATSCC) -o glHello glHello.dats $(ATSCTRB) -lGL -lglut

compall:: glDoubleBuffer
glDoubleBuffer: glDoubleBuffer.dats
	$(ATSCC) -o glDoubleBuffer glDoubleBuffer.dats $(ATSCTRB) -lGL -lglut

compall:: glIcosahedron
glIcosahedron: glIcosahedron.dats
	$(ATSCC) -D_ATS_GCATS -o glIcosahedron glIcosahedron.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

compall:: glClipping
glClipping: glClipping.dats
	$(ATSCC) -o glClipping glClipping.dats $(ATSCTRB) -lGL -lGLU -lglut

compall:: glCubeView
glCubeView: glCubeView.dats
	$(ATSCC) -o glCubeView glCubeView.dats $(ATSCTRB) -lGL -lGLU -lglut

compall:: glPlanet
glPlanet: glPlanet.dats
	$(ATSCC) -o glPlanet glPlanet.dats $(ATSCTRB) -lGL -lGLU -lglut

compall:: glColoredTriangle
glColoredTriangle: glColoredTriangle.dats
	$(ATSCC) -o glColoredTriangle glColoredTriangle.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

compall:: glLitSphere
glLitSphere: glLitSphere.dats
	$(ATSCC) -o glLitSphere glLitSphere.dats $(ATSCTRB) -lGL -lglut

compall:: glLightMove1
glLightMove1: glLightMove1.dats
	$(ATSCC) -o glLightMove1 glLightMove1.dats $(ATSCTRB) -lGL -lGLU -lglut

compall:: glLightMove2
glLightMove2: glLightMove2.dats
	$(ATSCC) -o glLightMove2 glLightMove2.dats $(ATSCTRB) -lGL -lGLU -lglut

compall:: glBlending1
glBlending1: glBlending1.dats
	$(ATSCC) -o glBlending1 glBlending1.dats $(ATSCTRB) -lGL -lGLU -lglut

compall:: glBlending2
glBlending2: glBlending2.dats
	$(ATSCC) -o glBlending2 glBlending2.dats $(ATSCTRB) -lGL -lglut

compall:: glDisplayList1
glDisplayList1: glDisplayList1.dats
	$(ATSCC) -o glDisplayList1 glDisplayList1.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

######

#
# A little bit animation for fun
#
compall:: glFaces
glFaces: glFaces.dats
	$(ATSCC) -o glFaces glFaces.dats $(ATSCTRB) -lGL -lglut -lm

######

#
# A simple game of Tetris implemented in ATS
#
compall:: glTetrix
glTetrix: glTetrix.dats
	$(ATSCC) -O2 -o glTetrix glTetrix.dats $(ATSCTRB) -lGL -lglut -lm

######

RMF=rm -f

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
