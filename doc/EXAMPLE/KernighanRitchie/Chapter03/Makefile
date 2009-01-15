all: \
  atoi \
  reverse \
  itoa \

######

html::
	atsopt --posmark_html_only -d atoi.dats
	atsopt --posmark_html_only -d reverse.dats
	atsopt --posmark_html_only -d itoa.dats

######

atoi: atoi.dats
	atscc -o atoi atoi.dats

reverse: reverse.dats
	atscc -o reverse reverse.dats

itoa: itoa.dats
	atscc -o itoa itoa.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f atoi
	rm -f reverse
	rm -f itoa

###### end of [Makefile] ######
