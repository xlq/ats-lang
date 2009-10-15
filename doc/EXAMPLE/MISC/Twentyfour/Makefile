##
## Makefile for [twentyfour.dats]
##

#GCFLAG=-D_ATS_gc // no longer in use
#GCFLAG=-D_ATS_gcats // no longer in use
GCFLAG=-D_ATS_GCATS
#GCFLAG=-D_ATS_GCBDW

ATSCC="$(ATSHOME)"/bin/atscc -Wall

######

checkall:: twentyfour cleanall

######

twentyfour: twentyfour.dats rational.dats rational.sats
	$(ATSCC) $(GCFLAG) -o twentyfour -O3 twentyfour.dats rational.dats rational.sats && \
        ./twentyfour

######

clean:: ; rm -f *_dats.c *_sats.c *~
cleanall: clean; rm -f twentyfour

###### end of [Makefile] ######
