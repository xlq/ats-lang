all: \
  fsize \

######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc
ATSOPT=$(or $(ATSHOME), "/usr")/bin/atsopt

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
