#
#
# Makefile for K&R examples in Chapter 5
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

compall:: getint
getint: getint.dats ; $(ATSCC) -o getint getint.dats

compall:: strlen
strlen: strlen.dats ; $(ATSCC) -o strlen strlen.dats

compall:: strcpy
strcpy: strcpy.dats ; $(ATSCC) -o strcpy strcpy.dats

compall:: strcmp
strcmp: strcmp.dats ; $(ATSCC) -o strcmp strcmp.dats

compall:: strcmp_alt
strcmp_alt: strcmp_alt.dats; $(ATSCC) -o strcmp_alt strcmp_alt.dats

compall:: month_name
month_name: month_name.dats ; $(ATSCC) -o month_name month_name.dats

compall:: month_day
month_day: month_day.dats ; $(ATSCC) -o month_day month_day.dats

######

html:: ; $(ATSOPT) --posmark_html -d getint.dats > getint_dats.html
html:: ; $(ATSOPT) --posmark_html -d strlen.dats > strlen_dats.html
html:: ; $(ATSOPT) --posmark_html -d strcpy.dats > strcpy_dats.html
html:: ; $(ATSOPT) --posmark_html -d strcmp.dats > strcmp_dats.html
html:: ; $(ATSOPT) --posmark_html -d strcmp_alt.dats > strcmp_alt_dats.html
html:: ; $(ATSOPT) --posmark_html -d month_name.dats > month_name_dats.html
html:: ; $(ATSOPT) --posmark_html -d month_day.dats > month_day_dats.html

######

RMF=rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall: clean
	$(RMF) *_?ats.html 
	$(RMF) getint
	$(RMF) strlen
	$(RMF) strcpy
	$(RMF) strcmp
	$(RMF) strcmp_alt
	$(RMF) month_name
	$(RMF) month_day

###### end of [Makefile] ######
