all: \
  strlen \
  rand \

######

html::
	atsopt --posmark_html -d strlen.dats
	atsopt --posmark_html -d rand.dats

######

strlen: strlen.dats
	atscc -o strlen strlen.dats

rand: rand.dats
	atscc -o rand rand.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f strlen
	rm -f rand

###### end of [Makefile] ######
