all: \
  fsize \

######

html::
	atsopt --posmark_html -d fsize.dats > fsize_dats.html

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
