all: \
  getword \

######

ATSOPT=$(ATSHOME)/bin/atsopt

######

html::
	$(ATSOPT) --posmark_html -d getword.dats > getword_dats.html

######

getword: getword.dats
	atscc -o getword getword.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f getword

###### end of [Makefile] ######
