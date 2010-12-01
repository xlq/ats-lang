#
#
# Makefile for K&R examples in Chapter 4
#
#

######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

checkall:: compall cleanall

######

compall:: atof
atof: atof.dats ; $(ATSCC) -o atof atof.dats

compall:: printd
printd: printd.dats ; $(ATSCC) -o printd printd.dats

compall:: qsort
qsort: qsort.dats ; $(ATSCC) -o qsort qsort.dats

######

html:: ; $(ATSOPT) --posmark_html -d atof.dats > atof_dats.html
html:: ; $(ATSOPT) --posmark_html -d printd.dats > printd_dats.html
html:: ; $(ATSOPT) --posmark_html -d qsort.dats > qsort_dats.html

######

RMF=rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) *_?ats.html 
	$(RMF) atof
	$(RMF) printd
	$(RMF) qsort

###### end of [Makefile] ######
