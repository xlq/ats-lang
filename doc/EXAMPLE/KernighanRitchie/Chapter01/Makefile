all: \
  hello \
  fahrenheit_celsius \
  echo \
  charcnt \
  linecnt \
  wc \
  dsocnt \
  power \
  longest_line \
  longest_line_alt \

######

html::
	atsopt --posmark_html_only -d hello.dats
	atsopt --posmark_html_only -d fahrenheit_celsius.dats
	atsopt --posmark_html_only -d echo.dats
	atsopt --posmark_html_only -d charcnt.dats
	atsopt --posmark_html_only -d linecnt.dats
	atsopt --posmark_html_only -d wc.dats
	atsopt --posmark_html_only -d digit_space_other_cnt.dats
	atsopt --posmark_html_only -d power.dats
	atsopt --posmark_html_only -d longest_line.dats
	atsopt --posmark_html_only -d longest_line_alt.dats

######

hello: hello.dats
	atscc -o hello hello.dats

fahrenheit_celsius: fahrenheit_celsius.dats
	atscc -o fahrenheit_celsius fahrenheit_celsius.dats

echo: echo.dats
	atscc -o echo echo.dats

charcnt: charcnt.dats
	atscc -o charcnt charcnt.dats

linecnt: linecnt.dats
	atscc -o linecnt linecnt.dats

wc: wc.dats
	atscc -o wc wc.dats

dsocnt: digit_space_other_cnt.dats
	atscc -o dsocnt digit_space_other_cnt.dats

power: power.dats
	atscc -o power power.dats

longest_line: longest_line.dats
	atscc -o longest_line longest_line.dats

longest_line_alt: longest_line_alt.dats
	atscc -o longest_line_alt longest_line_alt.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f hello
	rm -f fahrenheit_celsius
	rm -f echo
	rm -f charcnt
	rm -f linecnt
	rm -f wc
	rm -f dsocnt
	rm -f power
	rm -f longest_line
	rm -f longest_line_alt

###### end of [Makefile] ######
