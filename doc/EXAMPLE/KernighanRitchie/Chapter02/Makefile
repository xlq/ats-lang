all: \
  strlen \
  rand \

######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc
ATSOPT=$(or $(ATSHOME), "/usr")/bin/atsopt

######

html::
	$(ATSOPT) --posmark_html -d strlen.dats > strlen_dats.html
	$(ATSOPT) --posmark_html -d rand.dats > rand_dats.html

######

strlen: strlen.dats
	$(ATSCC) -o strlen strlen.dats

rand: rand.dats
	$(ATSCC) -o rand rand.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f strlen
	rm -f rand

###### end of [Makefile] ######
