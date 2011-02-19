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

depend:: ; $(ATSOPT) -o .depend -dep1 -s hello_module.sats
depend:: ; $(ATSOPT) -o .depend -dep1 -d hello_module.dats

include .depend

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c
clean:: ; $(RMF) *_?ats.o

cleanall:: clean

###### end of [Makefile] ######