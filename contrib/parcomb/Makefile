######
#
# Makefile for the [parcomb] package
#
######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc -Wall

######

SOURCES := \
  dynloadall.dats \
  parcomb.sats parcomb.dats \
  posloc.sats posloc.dats \
  tokenize.sats tokenize.dats \

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))

######

atsctrb_parcomb.o: $(OBJECTS); ld -r -o $@ $(OBJECTS)

######

dynloadall_dats.o: dynloadall.dats
	$(ATSCC) -O2 -c -o $@ $<

######

parcomb_sats.o: SATS/parcomb.sats
	$(ATSCC) -O2 -c -o parcomb_sats.o $<
parcomb_dats.o: DATS/parcomb.dats
	$(ATSCC) -O2 -c -o parcomb_dats.o $<

######

posloc_sats.o: SATS/posloc.sats
	$(ATSCC) -O2 -c -o posloc_sats.o $<
posloc_dats.o: DATS/posloc.dats
	$(ATSCC) -O2 -c -o posloc_dats.o $<

tokenize_sats.o: SATS/tokenize.sats
	$(ATSCC) -O2 -c -o tokenize_sats.o $<
tokenize_dats.o: DATS/tokenize.dats
	$(ATSCC) -O2 -c -o tokenize_dats.o $<

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall: clean
	$(RMF) atsctrb_parcomb.o

###### end of [Makefile] ######
