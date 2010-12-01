#
#
# Makefile for K&R examples in Chapter 3
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

compall:: atoi
atoi: atoi.dats ; $(ATSCC) -o atoi atoi.dats

compall:: reverse
reverse: reverse.dats ; $(ATSCC) -o reverse reverse.dats

compall:: itoa
itoa: itoa.dats ; $(ATSCC) -o itoa itoa.dats

######

html::
	$(ATSOPT) --posmark_html -d atoi.dats > atoi_dats.html
	$(ATSOPT) --posmark_html -d reverse.dats > reverse_dats.html
	$(ATSOPT) --posmark_html -d itoa.dats > itoa_dats.html

######

RMF=rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) *_?ats.html 
	$(RMF) atoi
	$(RMF) reverse
	$(RMF) itoa

###### end of [Makefile] ######
