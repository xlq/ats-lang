#
#
# Makefile for K&R examples in Chapter 4
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
  atof \
  printd \
  qsort \

######

html::
	$(ATSOPT) --posmark_html -d atof.dats > atof_dats.html
	$(ATSOPT) --posmark_html -d printd.dats > printd_dats.html
	$(ATSOPT) --posmark_html -d qsort.dats > qsort_dats.html

######

atof: atof.dats
	$(ATSCC) -o atof atof.dats

printd: printd.dats
	$(ATSCC) -o printd printd.dats

qsort: qsort.dats
	$(ATSCC) -o qsort qsort.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f atof
	rm -f printd
	rm -f qsort

###### end of [Makefile] ######
