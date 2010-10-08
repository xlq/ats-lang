#
#
# Makefile for K&R examples in Chapter 1
#
#

######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

checkall: compall cleanall

######

compall: \
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
	$(ATSOPT) --posmark_html -d hello.dats > hello_dats.html
	$(ATSOPT) --posmark_html -d fahrenheit_celsius.dats > fahrenheit_celsius_dats.html
	$(ATSOPT) --posmark_html -d echo.dats > echo_dats.html
	$(ATSOPT) --posmark_html -d charcnt.dats > charcnt_dats.html
	$(ATSOPT) --posmark_html -d linecnt.dats > linecnt_dats.html
	$(ATSOPT) --posmark_html -d wc.dats > wc_dats.html
	$(ATSOPT) --posmark_html -d digit_space_other_cnt.dats > digit_space_other_dats.html
	$(ATSOPT) --posmark_html -d power.dats > power_dats.html
	$(ATSOPT) --posmark_html -d longest_line.dats > longest_line_dats.html
	$(ATSOPT) --posmark_html -d longest_line_alt.dats > longest_line_alt_dats.html

######

hello: hello.dats
	$(ATSCC) -o hello hello.dats

fahrenheit_celsius: fahrenheit_celsius.dats
	$(ATSCC) -o fahrenheit_celsius fahrenheit_celsius.dats

echo: echo.dats
	$(ATSCC) -o echo echo.dats

charcnt: charcnt.dats
	$(ATSCC) -o charcnt charcnt.dats

linecnt: linecnt.dats
	$(ATSCC) -o linecnt linecnt.dats

wc: wc.dats
	$(ATSCC) -o wc wc.dats

dsocnt: digit_space_other_cnt.dats
	$(ATSCC) -o dsocnt digit_space_other_cnt.dats

power: power.dats
	$(ATSCC) -o power power.dats

longest_line: longest_line.dats
	$(ATSCC) -o longest_line longest_line.dats

longest_line_alt: longest_line_alt.dats
	$(ATSCC) -o longest_line_alt longest_line_alt.dats

######

RMF = rm -f

######

clean::
	$(RMF) a.out *_dats.c *.o *~

cleanall: clean
	$(RMF) *_dats.html 
	$(RMF) hello
	$(RMF) fahrenheit_celsius
	$(RMF) echo
	$(RMF) charcnt
	$(RMF) linecnt
	$(RMF) wc
	$(RMF) dsocnt
	$(RMF) power
	$(RMF) longest_line
	$(RMF) longest_line_alt

###### end of [Makefile] ######
