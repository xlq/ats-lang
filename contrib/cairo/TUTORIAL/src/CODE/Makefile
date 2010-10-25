#
# A simple Makefile
#

######

GCC = gcc

######

ATSHOMEQ = "$(ATSHOME)"
ATSCC = $(ATSHOMEQ)/bin/atscc
ATSOPT = $(ATSHOMEQ)/bin/atsopt

######

tutprog_hw: tutprog_hw.dats
	$(ATSCC) -o $@ tutprog_hw.dats `pkg-config cairo --cflags --libs`

tutprog_hw.dats: tutprog_hw.source
	$(GCC) -DINLINED=0 -C -E -P -o $@ -x c tutprog_hw.source

tutprog_hw_dats.db: tutprog_hw.source
	$(GCC) -DINLINED=1 -C -E -P -o $@ -x c tutprog_hw.source

######

tutprog_linecap: tutprog_linecap.dats
	$(ATSCC) -o $@ tutprog_linecap.dats `pkg-config cairo --cflags --libs`

tutprog_linejoin: tutprog_linejoin.dats
	$(ATSCC) -o $@ tutprog_linejoin.dats `pkg-config cairo --cflags --libs`

tutprog_showtext: tutprog_showtext.dats
	$(ATSCC) -o $@ tutprog_showtext.dats `pkg-config cairo --cflags --libs`

######

tutprog_sqrcirc: tutprog_sqrcirc.dats
	$(ATSCC) -o $@ tutprog_sqrcirc.dats `pkg-config cairo --cflags --libs`

tutprog_sqrcirc.dats: tutprog_sqrcirc.source
	$(GCC) -DINLINED=0 -C -E -P -o $@ -x c tutprog_sqrcirc.source

######

tutprog_triangle: tutprog_triangle.dats
	$(ATSCC) -o $@ tutprog_triangle.dats `pkg-config gtk+-2.0 --cflags --libs`

tutprog_triangle.dats: tutprog_triangle.source
	$(GCC) -DINLINED=0 -C -E -P -o $@ -x c tutprog_triangle.source

######

illucircmot: illucircmot.dats
	$(ATSCC) -o $@ illucircmot.dats `pkg-config cairo --cflags --libs`

illuwavy: illuwavy.dats
	$(ATSCC) -o $@ illuwavy.dats `pkg-config gtk+-2.0 --cflags --libs`

######

typecheck: \
  tc_tutprog_hw \
  tc_tutprog_linecap \
  tc_tutprog_linejoin \
  tc_tutprog_showtext \
  tc_tutprog_sqrcirc \
  tc_tutprog_triangle \
  tc_illucircmot \
  tc_illuwavy \

tc_tutprog_hw: tutprog_hw.dats; $(ATSOPT) --typecheck -d tutprog_hw.dats
tc_tutprog_linecap: tutprog_linecap.dats; $(ATSOPT) --typecheck -d tutprog_linecap.dats
tc_tutprog_linejoin: tutprog_linejoin.dats; $(ATSOPT) --typecheck -d tutprog_linejoin.dats
tc_tutprog_showtext: tutprog_showtext.dats; $(ATSOPT) --typecheck -d tutprog_showtext.dats
tc_tutprog_sqrcirc: tutprog_sqrcirc.dats; $(ATSOPT) --typecheck -d tutprog_sqrcirc.dats
tc_tutprog_triangle: tutprog_triangle.dats; $(ATSOPT) --typecheck -d tutprog_triangle.dats
tc_illucircmot: illucircmot.dats; $(ATSOPT) --typecheck -d illucircmot.dats
tc_illuwavy: illuwavy.dats; $(ATSOPT) --typecheck -d illuwavy.dats

######

clean::
	rm -f *~
	rm -f *_?ats.c *_?ats.o
	rm -f tutprog_hw tutprog_hw.dats
	rm -f tutprog_linecap
	rm -f tutprog_linejoin
	rm -f tutprog_showtext
	rm -f tutprog_sqrcirc tutprog_sqrcirc.dats
	rm -f tutprog_triangle tutprog_triangle.dats
	rm -f illuwavy illucircmot

cleanall: clean
	rm -f tutprog_hw.png
	rm -f tutprog_hw_dats.db
	rm -f tutprog_linejoin.png
	rm -f tutprog_showtext.png
	rm -f tutprog_sqrcirc.png

###### end of [Makefile] ######
