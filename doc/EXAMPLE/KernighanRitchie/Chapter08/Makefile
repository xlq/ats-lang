#
#
# Makefile for K&R examples in Chapter 8
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
  fsize \

######

html::
	$(ATSOPT) --posmark_html -d fsize.dats > fsize_dats.html

######

fsize: fsize.dats
	$(ATSCC) -o fsize fsize.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f fsize

###### end of [Makefile] ######
