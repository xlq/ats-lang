#
#
# Some Examples in ATS involving GTK+ programming
#
#

######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

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
  bsearch_demo \

######

#
# Please do the following
#   cd $ATSHOME/contrib/GTK; make atsctrb_GTK.o
# if "atsctrb_GTK.o" is not available
#
LIBATSGTK=$(ATSHOMEQ)/contrib/GTK/atsctrb_GTK.o
GameOf24: GameOf24.dats
	$(ATSCC) -D_ATS_GCATS -o $@ GameOf24.dats $(LIBATSGTK) $(GTKFLAGS) -lm

######

gtkcairoclock: gtkcairoclock.dats
	$(ATSCC) -Wl,-rpath,$(ATSHOMEQ)/ccomp/lib -o $@ gtkcairoclock.dats $(GTKFLAGS) -lm

######

gtkcairopascal: gtkcairopascal.dats
	$(ATSCC) -D_ATS_GCATS -o $@ gtkcairopascal.dats $(GTKFLAGS) -lm

######

ATSCTRB=$(ATSHOMEQ)/contrib/cairo/atsctrb_cairo.o
gtkcairodisc: gtkcairodisc.dats
	$(ATSCC) -D_ATS_GCATS $(ATSCTRB) -o $@ gtkcairodisc.dats $(GTKFLAGS) -lm

######

ATSCTRB=$(ATSHOMEQ)/contrib/cairo/atsctrb_cairo.o
bsearch_demo: bsearch_demo.dats
	$(ATSCC) -D_ATS_GCATS $(ATSCTRB) -o $@ bsearch_demo.dats $(GTKFLAGS) -lm

######

html::
	$(ATSOPT) --posmark_html -d GameOf24.dats > GameOf24_dats.html
	$(ATSOPT) --posmark_html -d gtkcairoclock.dats > gtkcairoclock_dats.html
	$(ATSOPT) --posmark_html -d gtkcairopascal.dats > gtkcairopascal_dats.html
	$(ATSOPT) --posmark_html -d gtkcairopascal.dats > gtkcairopascal_dats.html
	$(ATSOPT) --posmark_html -d bsearch_demo.dats > bsearch_demo_dats.html

######

xref::
	$(ATSOPT) --posmark_xref=XREF -d \
          $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
	$(ATSOPT) --posmark_xref=XREF -d GameOf24.dats > GameOf24_dats.html
	$(ATSOPT) --posmark_xref=XREF -d gtkcairoclock.dats > gtkcairoclock_dats.html
	$(ATSOPT) --posmark_xref=XREF -d gtkcairopascal.dats > gtkcairopascal_dats.html
	$(ATSOPT) --posmark_xref=XREF -d gtkcairopascal.dats > gtkcairopascal_dats.html
	$(ATSOPT) --posmark_xref=XREF -d bsearch_demo.dats > bsearch_demo_dats.html

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c

cleanall:: clean
	$(RMF) ./XREF/*
	$(RMF) ./*_?ats.html
	$(RMF) GameOf24
	$(RMF) gtkcairoclock
	$(RMF) gtkcairopascal
	$(RMF) gtkcairodisc
	$(RMF) bsearch_demo

###### end of [Makefile] ######
