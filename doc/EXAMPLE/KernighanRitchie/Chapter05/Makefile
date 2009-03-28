all: \
  getint \
  strlen \
  strcpy \
  strcmp \
  strcmp_alt \
  month_name \
  month_day \

######

ATSOPT=$(ATSHOME)/bin/atsopt

######

html::
	$(ATSOPT) --posmark_html -d getint.dats > getint_dats.html
	$(ATSOPT) --posmark_html -d strlen.dats > strlen_dats.html
	$(ATSOPT) --posmark_html -d strcpy.dats > strcpy_dats.html
	$(ATSOPT) --posmark_html -d strcmp.dats > strcmp_dats.html
	$(ATSOPT) --posmark_html -d strcmp_alt.dats > strcmp_alt_dats.html
	$(ATSOPT) --posmark_html -d month_name.dats > month_name_dats.html
	$(ATSOPT) --posmark_html -d month_day.dats > month_day_dats.html

######

getint: getint.dats
	atscc -o getint getint.dats

strlen: strlen.dats
	atscc -o strlen strlen.dats

strcpy: strcpy.dats
	atscc -o strcpy strcpy.dats

strcmp: strcmp.dats
	atscc -o strcmp strcmp.dats

strcmp_alt: strcmp_alt.dats
	atscc -o strcmp_alt strcmp_alt.dats

month_name: month_name.dats
	atscc -o month_name month_name.dats

month_day: month_day.dats
	atscc -o month_day month_day.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f getint
	rm -f strlen
	rm -f strcpy
	rm -f strcmp
	rm -f strcmp_alt
	rm -f month_name
	rm -f month_day

###### end of [Makefile] ######
