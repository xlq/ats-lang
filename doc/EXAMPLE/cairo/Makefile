#
#
# Some Examples in ATS involving GTK+ programming
#
#

######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc
ATSOPT=$(or $(ATSHOME), "/usr")/bin/atsopt
XRCFLAGS=`pkg-config cairo --cflags`
GTKCLFLAGS=`pkg-config gtk+-2.0 --cflags --libs`

######

.PHONY: all
all: checkall

######

checkall:: compall cleanall

compall:: \
  blurring \
  clip-all \
  push-group \
  stroke-image \
  testcairo \
  text-rotate \
  text-transform \

######

blurring: blurring.dats blur_image_surface.o
	$(ATSCC) -o $@ blurring.dats blur_image_surface.o $(GTKCLFLAGS)

blur_image_surface.o: blur_image_surface.dats
	$(ATSCC) -c -o $@ blur_image_surface.dats $(XRCFLAGS)

######

clip-all: clip-all.dats
	$(ATSCC) -o $@ clip-all.dats $(GTKCLFLAGS)

######

push-group: push-group.dats
	$(ATSCC) -g -o $@ push-group.dats $(GTKCLFLAGS)

######

stroke-image: stroke-image.dats
	$(ATSCC) -o $@ stroke-image.dats $(GTKCLFLAGS)

######

testcairo: testcairo.dats
	$(ATSCC) -o $@ testcairo.dats $(GTKCLFLAGS)

######

text-rotate: text-rotate.dats
	$(ATSCC) -o $@ text-rotate.dats $(GTKCLFLAGS)

text-transform: text-transform.dats
	$(ATSCC) -o $@ text-transform.dats $(GTKCLFLAGS)

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall:: clean
	rm -f blurring
	rm -f blur_image_surface.o
	rm -f clip-all
	rm -f push-group
	rm -f stroke-image
	rm -f testcairo
	rm -f text-rotate
	rm -f text-transform

###### end of [Makefile] ######
