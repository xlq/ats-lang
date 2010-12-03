#
#
# Some Examples in ATS involving GTK+ programming
#
#

######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

XRCFLAGS=`pkg-config cairo --cflags`
GTKCLFLAGS=`pkg-config gtk+-2.0 --cflags --libs`

######

.PHONY: all
all: checkall

######

checkall: compall cleanall

######

compall:: blurring
blurring: blurring.dats blur_image_surface.o
	$(ATSCC) -o $@ blurring.dats blur_image_surface.o $(GTKCLFLAGS) -lm
blur_image_surface.o: blur_image_surface.dats
	$(ATSCC) -c -o $@ blur_image_surface.dats $(XRCFLAGS)

######

compall:: clip-all
clip-all: clip-all.dats
	$(ATSCC) -o $@ clip-all.dats $(GTKCLFLAGS)

######

compall:: push-group
push-group: push-group.dats
	$(ATSCC) -g -o $@ push-group.dats $(GTKCLFLAGS)

######

compall:: stroke-image
stroke-image: stroke-image.dats
	$(ATSCC) -o $@ stroke-image.dats $(GTKCLFLAGS)

######

compall:: testcairo
testcairo: testcairo.dats
	$(ATSCC) -o $@ testcairo.dats $(GTKCLFLAGS) -lm

######

compall:: text-rotate
text-rotate: text-rotate.dats
	$(ATSCC) -o $@ text-rotate.dats $(GTKCLFLAGS) -lm

compall:: text-transform
text-transform: text-transform.dats
	$(ATSCC) -o $@ text-transform.dats $(GTKCLFLAGS) -lm

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) blurring
	$(RMF) blur_image_surface.o
	$(RMF) clip-all
	$(RMF) push-group
	$(RMF) stroke-image
	$(RMF) testcairo
	$(RMF) text-rotate
	$(RMF) text-transform

###### end of [Makefile] ######
