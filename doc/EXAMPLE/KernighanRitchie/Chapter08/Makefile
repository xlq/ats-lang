all: \
  fsize \

######

html::
	atsopt --posmark_html_only -d fsize.dats

######

fsize: fsize.dats
	atscc -o fsize fsize.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f fsize

###### end of [Makefile] ######
