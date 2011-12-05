#
# A simple Makefile
#

######

ATSUSRQ="$(ATSHOME)"

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRBGL=$(ATSUSRQ)/contrib/GL/atsctrb_GL.o
ATSCTRBXR=$(ATSUSRQ)/contrib/cairo/atsctrb_cairo.o
ATSCTRBGTK=$(ATSUSRQ)/contrib/GTK/atsctrb_GTK.o
ATSCTRBPSLIDE=$(ATSUSRQ)/contrib/atspslide/atsctrb_atspslide.o

######

all:: myslide

######

GTKGLEXT=`pkg-config --cflags --libs gtk+-2.0 gtkglext-1.0 gtkglext-x11-1.0`
bin/ViewsViewtypesPresent: ViewsViewtypesPresent.dats ; \
  $(ATSCC) -O3 -o $@ $< $(ATSCTRBGL) $(ATSCTRBXR) $(ATSCTRBGTK) $(ATSCTRBPSLIDE) $(GTKGLEXT)

######

ViewsViewtypes.dvi: ViewsViewtypes.tex; pslatex $<
ViewsViewtypes.ps: ViewsViewtypes.dvi; dvips -P cmz -t letter -o $@ $<

##
## This for generating image data for the slide presentation
##

myslide: ViewsViewtypes.ps
	gs -r121x93 -g1024x1024 \
         -dNOPAUSE -sDEVICE=png256 \
         -sOutputFile='data/$@_'%d.png \
         -c "<</Orientation 3>> setpagedevice" \
         -q -dBATCH ViewsViewtypes.ps

######

clean:
	rm -f *~
	rm -f *_?ats.o
	rm -f *_?ats.c
	rm -f *.aux
	rm -f *.log
	rm -f *.out
	rm -f *.dvi

cleanall: clean
	rm -f data/myslide_*.png

###### end of [Makefile] ######
