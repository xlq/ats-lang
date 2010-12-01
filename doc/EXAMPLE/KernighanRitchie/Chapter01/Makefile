#
#
# Makefile for K&R examples in Chapter 1
#
#

######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

checkall: compall cleanall

######

compall:: hello
hello: hello.dats
	$(ATSCC) -o hello hello.dats

compall:: fahrenheit_celsius
fahrenheit_celsius: fahrenheit_celsius.dats
	$(ATSCC) -o fahrenheit_celsius fahrenheit_celsius.dats

compall:: echo
echo: echo.dats ; $(ATSCC) -o echo echo.dats

compall:: charcnt
charcnt: charcnt.dats ; $(ATSCC) -o charcnt charcnt.dats

compall:: linecnt
linecnt: linecnt.dats ; $(ATSCC) -o linecnt linecnt.dats

compall:: wc
wc: wc.dats ; $(ATSCC) -o wc wc.dats

compall:: dsocnt
dsocnt: digit_space_other_cnt.dats
	$(ATSCC) -o dsocnt digit_space_other_cnt.dats

compall:: power
power: power.dats ; $(ATSCC) -o power power.dats

compall:: longest_line
longest_line: longest_line.dats
	$(ATSCC) -o longest_line longest_line.dats

compall:: longest_line_alt
longest_line_alt: longest_line_alt.dats
	$(ATSCC) -o longest_line_alt longest_line_alt.dats

######

html:: ; $(ATSOPT) --posmark_html -d hello.dats > hello_dats.html
html:: ; $(ATSOPT) --posmark_html -d fahrenheit_celsius.dats > fahrenheit_celsius_dats.html
html:: ; $(ATSOPT) --posmark_html -d echo.dats > echo_dats.html
html:: ; $(ATSOPT) --posmark_html -d charcnt.dats > charcnt_dats.html
html:: ; $(ATSOPT) --posmark_html -d linecnt.dats > linecnt_dats.html
html:: ; $(ATSOPT) --posmark_html -d wc.dats > wc_dats.html
html:: ; $(ATSOPT) --posmark_html -d digit_space_other_cnt.dats > digit_space_other_dats.html
html:: ; $(ATSOPT) --posmark_html -d power.dats > power_dats.html
html:: ; $(ATSOPT) --posmark_html -d longest_line.dats > longest_line_dats.html
html:: ; $(ATSOPT) --posmark_html -d longest_line_alt.dats > longest_line_alt_dats.html

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall: clean
	$(RMF) *_?ats.html 
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
