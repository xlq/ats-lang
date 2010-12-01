#
#
# Makefile for K&R examples in Chapter 6
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

checkall: compall cleanall

######

compall:: getword
getword: getword.dats ; $(ATSCC) -o getword getword.dats

######

html:: ; $(ATSOPT) --posmark_html -d getword.dats > getword_dats.html

######

RMF=rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) *_?ats.html 
	$(RMF) getword

###### end of [Makefile] ######
