#
# A simple Makefile
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

IATSFLAGS=-IATS $(ATSHOME)/contrib/linux

######

%_sats.c: %.sats ; $(ATSOPT) $(IATSFLAGS) -o $@ -s $<
%_dats.c: %.dats ; $(ATSOPT) $(IATSFLAGS) -o $@ -d $<

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c
clean:: ; $(RMF) *_?ats.o

cleanall:: clean

###### end of [Makefile] ######