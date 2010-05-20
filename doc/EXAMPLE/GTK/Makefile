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
all: checkall

######

checkall:: compall cleanall

compall:: \
  GameOf24 \
  gtkcairoclock \

######

#
# Please do the following
#   cd $ATSHOME/contrib/GTK; make atsctrb_GTK.o
# if "atsctrb_GTK.o" is not available
#
LIBATSGTK=$(ATSHOME)/contrib/GTK/atsctrb_GTK.o
GameOf24: GameOf24.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $(GTKFLAGS) GameOf24.dats $(LIBATSGTK)

######

gtkcairoclock: gtkcairoclock.dats
	$(ATSCC) -o $@ gtkcairoclock.dats $(GTKFLAGS)

######

html::
	$(ATSOPT) --posmark_html -d GameOf24.dats > GameOf24_dats.html
	$(ATSOPT) --posmark_html -d gtkcairoclock.dats > gtkcairoclock_dats.html

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall:: clean
	rm -f GameOf24
	rm -f GameOf24_dats.html
	rm -f gtkcairoclock
	rm -f gtkcairoclock_dats.html

###### end of [Makefile] ######
