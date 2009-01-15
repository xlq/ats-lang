all: \
  getint \
  strlen \
  strcpy \
  strcmp \
  strcmp_alt \
  month_name \
  month_day \

######

html::
	atsopt --posmark_html_only -d getint.dats
	atsopt --posmark_html_only -d strlen.dats
	atsopt --posmark_html_only -d strcpy.dats
	atsopt --posmark_html_only -d strcmp.dats
	atsopt --posmark_html_only -d strcmp_alt.dats
	atsopt --posmark_html_only -d month_name.dats
	atsopt --posmark_html_only -d month_day.dats

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
