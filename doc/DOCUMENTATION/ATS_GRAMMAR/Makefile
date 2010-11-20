#
#
# A simple Makefile for documenting the grammar of ATS
#
#

######

ATSGRAMMAR=$(ATSHOME)/utils/atsgrammar/atsgrammar

######

all:: \
  atsgrammar_desc.html \
  atsgrammar_yats.html \

######

atsgrammar_desc.html: ; $(ATSGRAMMAR) --format=desc_html > $@
atsgrammar_yats.html: ; $(ATSGRAMMAR) --format=yats_html > $@

######

RMF = rm -f

######

clean::
	$(RMF) *~

cleanall:: clean
	$(RMF) atsgrammar_desc.html
	$(RMF) atsgrammar_yats.html

###### end of [Makefile] ######
