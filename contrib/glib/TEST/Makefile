#
#
# A simple Makefile for some glib testing code
#
#

######

ATSCC=$(ATSHOME)/bin/atscc

GLIBINC=/usr/lib/glib-2.0/include
#GLIBINC=/usr/lib64/glib-2.0/include

INCLUDES= \
  -I $(GLIBINC) \
  -I /usr/include/glib-2.0 \

INCLUDES_ATS= \
  -IATS $(GLIBINC) \
  -IATS /usr/include/glib-2.0 \

ATSCTRB=$(ATSHOME)/contrib/glib/atsctrb_glib.o

######

all: \
  garray-test \
  glist-test \
  gqsort-test \
  gstring-test \
  cleanall \

######

garray-test: garray-test.dats
	$(ATSCC) -O3 \
  $(INCLUDES) $(INCLUDES_ATS) \
  -o garray-test garray-test.dats \
  $(ATSCTRB) -lglib-2.0 \
  && ./garray-test

######

glist-test: glist-test.dats
	$(ATSCC) -O3 \
  $(INCLUDES) $(INCLUDES_ATS) \
  -o glist-test glist-test.dats \
  $(ATSCTRB) -lglib-2.0 \
  && ./glist-test

######

gqsort-test: gqsort-test.dats
	$(ATSCC) -O3 \
  $(INCLUDES) $(INCLUDES_ATS) \
  -o gqsort-test gqsort-test.dats \
  $(ATSCTRB) -lglib-2.0 \
  && ./gqsort-test

######

gstring-test: gstring-test.dats
	$(ATSCC) -O3 \
  $(INCLUDES) $(INCLUDES_ATS) \
  -o gstring-test gstring-test.dats \
  $(ATSCTRB) -lglib-2.0 \
  && ./gstring-test

######

clean::
	rm -f *~
	rm -f *_?ats.c *_?ats.o

cleanall: clean
	rm -f garray-test
	rm -f glist-test
	rm -f gqsort-test
	rm -f gstring-test

###### end of [Makefile] ######
