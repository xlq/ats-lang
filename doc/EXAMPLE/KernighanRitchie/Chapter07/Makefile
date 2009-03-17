all: \
  lower \
  fgets \
  filecopy \

######

html::
	atsopt --posmark_html -d lower.dats
	atsopt --posmark_html -d fgets.dats
	atsopt --posmark_html -d filecopy.dats

######

lower: lower.dats
	atscc -o lower lower.dats

fgets: fgets.dats
	atscc -o fgets fgets.dats

filecopy: filecopy.dats
	atscc -o filecopy filecopy.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f lower
	rm -f fgets
	rm -f filecopy

###### end of [Makefile] ######
