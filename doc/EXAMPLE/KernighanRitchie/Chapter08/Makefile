#
#
# Makefile for K&R examples in Chapter 8
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

compall:: fsize
fsize: fsize.dats ; $(ATSCC) -o fsize fsize.dats

######

html:: ; $(ATSOPT) --posmark_html -d fsize.dats > fsize_dats.html

######

RMF=rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) *_?ats.html 
	$(RMF) fsize

###### end of [Makefile] ######
