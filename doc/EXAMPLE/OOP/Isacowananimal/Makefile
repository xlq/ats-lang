##
##
## An interesting example found at http://merd.sourceforge.net
##
## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Time: November, 2010
##
##

######

ATSCC=$(ATSHOME)/bin/atscc

######

isacowananimal: \
  isacowananimal.sats isacowananimal.dats
	$(ATSCC) -g -o $@ \
  isacowananimal.sats isacowananimal.dats && ./isacowananimal

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) isacowananimal

######
