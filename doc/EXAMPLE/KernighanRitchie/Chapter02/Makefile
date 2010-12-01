#
#
# Makefile for K&R examples in Chapter 2
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

compall:: strlen
strlen: strlen.dats ; $(ATSCC) -o strlen strlen.dats

compall:: rand
rand: rand.dats ; $(ATSCC) -o rand rand.dats

######

html:: ; $(ATSOPT) --posmark_html -d strlen.dats > strlen_dats.html
html:: ; $(ATSOPT) --posmark_html -d rand.dats > rand_dats.html

######

RMF=rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) *_?ats.html 
	$(RMF) strlen
	$(RMF) rand

###### end of [Makefile] ######
