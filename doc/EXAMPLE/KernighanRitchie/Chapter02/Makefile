#
#
# Makefile for K&R examples in Chapter 2
#
#

######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean
cleanall:: ; $(RMF) *_?ats.html 

######

checkall:: strlen
cleanall:: ; $(RMF) strlen
strlen: strlen.dats ; $(ATSCC) -o strlen strlen.dats

checkall:: rand
cleanall:: ; $(RMF) rand
rand: rand.dats ; $(ATSCC) -o rand rand.dats

######

html:: ; $(ATSOPT) --posmark_html -d strlen.dats > strlen_dats.html
html:: ; $(ATSOPT) --posmark_html -d rand.dats > rand_dats.html

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

###### end of [Makefile] ######
