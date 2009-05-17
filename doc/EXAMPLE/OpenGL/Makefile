#
#
# Some programs involving OpenGL
#
#

ATSCC="$(ATSHOME)"/bin/atscc

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
	$(ATSCC) -o glHello glHello.dats -lGL -lglut

glDoubleBuffer: glDoubleBuffer.dats
	$(ATSCC) -o glDoubleBuffer glDoubleBuffer.dats -lGL -lglut

glIcosahedron: glIcosahedron.dats
	$(ATSCC) -D_ATS_GCATS -o glIcosahedron glIcosahedron.dats -lGL -lglut

glClipping: glClipping.dats
	$(ATSCC) -o glClipping glClipping.dats -lGL -lglut

glCubeView: glCubeView.dats
	$(ATSCC) -o glCubeView glCubeView.dats -lGL -lglut

glPlanet: glPlanet.dats
	$(ATSCC) -o glPlanet glPlanet.dats -lGL -lglut

glColoredTriangle: glColoredTriangle.dats
	$(ATSCC) -o glColoredTriangle glColoredTriangle.dats -lGL -lglut

glLitSphere: glLitSphere.dats
	$(ATSCC) -o glLitSphere glLitSphere.dats -lGL -lglut

glLightMove1: glLightMove1.dats
	$(ATSCC) -o glLightMove1 glLightMove1.dats -lGL -lglut

glLightMove2: glLightMove2.dats
	$(ATSCC) -o glLightMove2 glLightMove2.dats -lGL -lglut

glBlending1: glBlending1.dats
	$(ATSCC) -o glBlending1 glBlending1.dats -lGL -lglut

glBlending2: glBlending2.dats
	$(ATSCC) -o glBlending2 glBlending2.dats -lGL -lglut

glDisplayList1: glDisplayList1.dats
	$(ATSCC) -o glDisplayList1 glDisplayList1.dats -lGL -lglut

#
# A little bit animation for fun
#
glFaces: glFaces.dats
	$(ATSCC) -o glFaces glFaces.dats -lGL -lglut

#
# A simple game of Tetris implemented in ATS
#
glTetrix: glTetrix.dats
	$(ATSCC) -O2 -o glTetrix glTetrix.dats -lGL -lglut

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
 

