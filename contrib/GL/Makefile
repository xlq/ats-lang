#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: December, 2009
#

ATSCC="$(ATSHOME)"/bin/atscc

######

atsctrb_GL.o: gl_sats.o glut_sats.o
	ld -r -o $@ gl_sats.o glut_sats.o

######

gl_sats.o: SATS/gl.sats
	atscc -o $@ -c SATS/gl.sats
glut_sats.o: SATS/glut.sats
	atscc -o $@ -c SATS/glut.sats

######

clean::
	rm -f gl_sats.c gl_sats.o
	rm -f glut_sats.c glut_sats.o

cleanall: clean
	rm -f atsctrb_GL.o

###### end of [Makefile] ######
