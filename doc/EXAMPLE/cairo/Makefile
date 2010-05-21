#
#
# Some Examples in ATS involving GTK+ programming
#
#

######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc
ATSOPT=$(or $(ATSHOME), "/usr")/bin/atsopt
XRFLAGS=`pkg-config cairo --cflags --libs`
GTKFLAGS=`pkg-config gtk+-2.0 --cflags --libs`

######

.PHONY: all
all: checkall

######

checkall:: compall cleanall

compall:: \
  clip-all.dats \
  push-group.dats \
  stroke-image.dats \
  testcairo \
  text-rotate \
  text-transform \

######

clip-all: clip-all.dats
	$(ATSCC) -o $@ clip-all.dats $(GTKFLAGS)

######

push-group: push-group.dats
	$(ATSCC) -g -o $@ push-group.dats $(GTKFLAGS)

######

stroke-image: stroke-image.dats
	$(ATSCC) -o $@ stroke-image.dats $(GTKFLAGS)

######

testcairo: testcairo.dats
	$(ATSCC) -o $@ testcairo.dats $(GTKFLAGS)

######

text-rotate: text-rotate.dats
	$(ATSCC) -o $@ text-rotate.dats $(GTKFLAGS)

text-transform: text-transform.dats
	$(ATSCC) -o $@ text-transform.dats $(GTKFLAGS)

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall:: clean
	rm -f clip-all
	rm -f push-group
	rm -f stroke-image
	rm -f testcairo
	rm -f text-rotate
	rm -f text-transform

###### end of [Makefile] ######
