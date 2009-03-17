all: \
  atof \
  printd \
  qsort \

######

html::
	atsopt --posmark_html -d atof.dats
	atsopt --posmark_html -d printd.dats
	atsopt --posmark_html -d qsort.dats

######

atof: atof.dats
	atscc -o atof atof.dats

printd: printd.dats
	atscc -o printd printd.dats

qsort: qsort.dats
	atscc -o qsort qsort.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f atof
	rm -f printd
	rm -f qsort

###### end of [Makefile] ######
