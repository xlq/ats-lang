#
#
# Makefile for some K&R examples
#
#

######

.PHONY: all
all:: checkall

######

checkall::
	cd Chapter01; make checkall
	cd Chapter02; make checkall
	cd Chapter03; make checkall
	cd Chapter04; make checkall
	cd Chapter05; make checkall
	cd Chapter06; make checkall
	cd Chapter07; make checkall
	cd Chapter08; make checkall

######

compall:
	cd Chapter01; make compall
	cd Chapter02; make compall
	cd Chapter03; make compall
	cd Chapter04; make compall
	cd Chapter05; make compall
	cd Chapter06; make compall
	cd Chapter07; make compall
	cd Chapter08; make compall

######

html::
	cd Chapter01; make html
	cd Chapter02; make html
	cd Chapter03; make html
	cd Chapter04; make html
	cd Chapter05; make html
	cd Chapter06; make html
	cd Chapter07; make html
	cd Chapter08; make html  

######

update:: update01 update02 update03 update04 update05 update06 update07 update08

update01::
	scp Chapter01/*.dats Chapter01/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter01

update02::
	scp Chapter02/*.dats Chapter02/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter02

update03::
	scp Chapter03/*.dats Chapter03/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter03

update04::
	scp Chapter04/*.dats Chapter04/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter04

update05::
	scp Chapter05/*.dats Chapter05/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter05

update06::
	scp Chapter06/*.dats Chapter06/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter06

update07::
	scp Chapter07/*.dats Chapter07/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter07

update08::
	scp Chapter08/*.dats Chapter08/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter08

######

cleanall:
	cd Chapter01; make cleanall
	cd Chapter02; make cleanall
	cd Chapter03; make cleanall
	cd Chapter04; make cleanall
	cd Chapter05; make cleanall
	cd Chapter06; make cleanall
	cd Chapter07; make cleanall
	cd Chapter08; make cleanall

###### end of [Makefile]

