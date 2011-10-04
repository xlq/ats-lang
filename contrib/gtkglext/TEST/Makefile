#
#
# A simple Makefile for some programs involving OpenGL
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#
#

######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRB=$(ATSUSRQ)/contrib/GL/atsctrb_GL.o
ATSCTRBGTK=$(ATSUSRQ)/contrib/GTK/atsctrb_GTK.o

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

GTKGLEXT=`pkg-config --cflags --libs gtk+-2.0 gtkglext-1.0 gtkglext-x11-1.0`

######

checkall:: gtkglHello
cleanall:: ; $(RMF) gtkglHello
gtkglHello: gtkglHello.dats
	$(ATSCC) -o gtkglHello gtkglHello.dats $(ATSCTRB) $(ATSCTRBGTK) $(GTKGLEXT)

######

checkall:: gtkglFaces
cleanall:: ; $(RMF) gtkglFaces
gtkglFaces: gtkglFaces.dats
	$(ATSCC) -o gtkglFaces gtkglFaces.dats $(ATSCTRB) $(ATSCTRBGTK) $(GTKGLEXT)

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c
	$(RMF) *_?ats.o

###### end of [Makefile] ######
