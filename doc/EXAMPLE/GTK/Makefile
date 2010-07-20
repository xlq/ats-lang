#
#
# Some Examples in ATS involving GTK+ programming
#
#

######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc
ATSOPT=$(or $(ATSHOME), "/usr")/bin/atsopt
GTKFLAGS=`pkg-config gtk+-2.0 --cflags --libs`

######

.PHONY: all
all:: checkall

######

checkall:: compall cleanall

compall:: \
  GameOf24 \
  gtkcairoclock \
  gtkcairopascal \
  gtkcairodisc \

######

#
# Please do the following
#   cd $ATSHOME/contrib/GTK; make atsctrb_GTK.o
# if "atsctrb_GTK.o" is not available
#
LIBATSGTK=$(ATSHOME)/contrib/GTK/atsctrb_GTK.o
GameOf24: GameOf24.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $(GTKFLAGS) GameOf24.dats $(LIBATSGTK) -lm

######

gtkcairoclock: gtkcairoclock.dats
	$(ATSCC) -o $@ gtkcairoclock.dats $(GTKFLAGS) -lm

######

gtkcairopascal: gtkcairopascal.dats
	$(ATSCC) -D_ATS_GCATS -o $@ gtkcairopascal.dats $(GTKFLAGS) -lm

######

gtkcairodisc: gtkcairodisc.dats
	$(ATSCC) -D_ATS_GCATS -o $@ gtkcairodisc.dats $(GTKFLAGS) -lm

######

html::
	$(ATSOPT) --posmark_html -d GameOf24.dats > GameOf24_dats.html
	$(ATSOPT) --posmark_html -d gtkcairoclock.dats > gtkcairoclock_dats.html
	$(ATSOPT) --posmark_html -d gtkcairopascal.dats > gtkcairopascal_dats.html
	$(ATSOPT) --posmark_html -d gtkcairopascal.dats > gtkcairopascal_dats.html

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall:: clean
	rm -f GameOf24 GameOf24_dats.html
	rm -f gtkcairoclock gtkcairoclock_dats.html
	rm -f gtkcairopascal gtkcairopascal_dats.html
	rm -f gtkcairodisc gtkcairodisc_dats.html

###### end of [Makefile] ######
