#
#
# Makefile for K&R examples in Chapter 7
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

compall:: lower
lower: lower.dats ; $(ATSCC) -o lower lower.dats

compall:: fgets
fgets: fgets.dats ; $(ATSCC) -o fgets fgets.dats

filecopy: filecopy.dats ; $(ATSCC) -o filecopy filecopy.dats
compall:: filecopy

######

html:: ; $(ATSOPT) --posmark_html -d lower.dats > lower_dats.html
html:: ; $(ATSOPT) --posmark_html -d fgets.dats > fgets_dats.html
html:: ; $(ATSOPT) --posmark_html -d filecopy.dats > filecopy_dats.html

######

RMF=rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) *_?ats.html 
	$(RMF) lower
	$(RMF) fgets
	$(RMF) filecopy

###### end of [Makefile] ######
