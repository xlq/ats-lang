#
#
# A simple Makefile for some glib testing code
#
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.3"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRB=$(ATSLIBQ)/contrib/glib/atsctrb_glib.o

######

GLIBINC=/usr/lib/glib-2.0/include
GLIBINC=/usr/lib64/glib-2.0/include

INCLUDES= \
  -I $(GLIBINC) \
  -I /usr/include/glib-2.0 \

INCLUDES_ATS= \
  -IATS $(GLIBINC) \
  -IATS /usr/include/glib-2.0 \

######

.PHONY: all

######

all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: garray-test
garray-test: garray-test.dats
	$(ATSCC) -O3 \
  $(INCLUDES) $(INCLUDES_ATS) \
  -o garray-test garray-test.dats \
  $(ATSCTRB) -lglib-2.0 \
  && ./garray-test
cleanall:: ; $(RMF) garray-test

######

checkall:: glist-test
glist-test: glist-test.dats
	$(ATSCC) -O3 \
  $(INCLUDES) $(INCLUDES_ATS) \
  -o glist-test glist-test.dats \
  $(ATSCTRB) -lglib-2.0 \
  && ./glist-test
cleanall:: ; $(RMF) glist-test

######

checkall:: gqsort-test
gqsort-test: gqsort-test.dats
	$(ATSCC) -O3 \
  $(INCLUDES) $(INCLUDES_ATS) \
  -o gqsort-test gqsort-test.dats \
  $(ATSCTRB) -lglib-2.0 \
  && ./gqsort-test
cleanall:: ; $(RMF) gqsort-test

######

checkall:: gstring-test
gstring-test: gstring-test.dats
	$(ATSCC) -O3 \
  $(INCLUDES) $(INCLUDES_ATS) \
  -o gstring-test gstring-test.dats \
  $(ATSCTRB) -lglib-2.0 \
  && ./gstring-test
cleanall:: ; $(RMF) gstring-test

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

###### end of [Makefile] ######
