#
#
# Makefile for K&R examples in Chapter 6
#
#

######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

checkall: compall cleanall

######

compall: \
  getword \

######

html::
	$(ATSOPT) --posmark_html -d getword.dats > getword_dats.html

######

getword: getword.dats
	$(ATSCC) -o getword getword.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f getword

###### end of [Makefile] ######
