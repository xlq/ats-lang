#
#
# Makefile for K&R examples in Chapter 7
#
#

######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

all: \
  lower \
  fgets \
  filecopy \

######

html::
	$(ATSOPT) --posmark_html -d lower.dats > lower_dats.html
	$(ATSOPT) --posmark_html -d fgets.dats > fgets_dats.html
	$(ATSOPT) --posmark_html -d filecopy.dats > filecopy_dats.html

######

lower: lower.dats
	$(ATSCC) -o lower lower.dats

fgets: fgets.dats
	$(ATSCC) -o fgets fgets.dats

filecopy: filecopy.dats
	$(ATSCC) -o filecopy filecopy.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f lower
	rm -f fgets
	rm -f filecopy

###### end of [Makefile] ######
