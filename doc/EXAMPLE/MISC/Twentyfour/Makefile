##
## Makefile for [twentyfour.dats]
##

#GCFLAG=-D_ATS_gc
#GCFLAG=-D_ATS_gcats
GCFLAG=-D_ATS_GCATS

ATSCC="$(ATSHOME)"/bin/atscc

######

twentyfour: twentyfour.dats rational.dats rational.sats
	$(ATSCC) $(GCFLAG) -o twentyfour -O3 twentyfour.dats rational.dats rational.sats

######

clean:: ; rm -f *_dats.c *_sats.c *~
cleanall: clean; rm -f twentyfour

###### end of [Makefile] ######
