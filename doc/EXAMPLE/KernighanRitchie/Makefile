#
#
# Makefile for some K&R examples
#
#

######

.PHONY: all
all:: checkall

######

checkall:: \
  compall \
  Chapter01 Chapter02 Chapter03 Chapter04 Chapter05 Chapter06 Chapter07 Chapter08 

######

Chapter01::
	cd Chapter01; make html

Chapter02::
	cd Chapter02; make html

Chapter03::
	cd Chapter03; make html

Chapter04::
	cd Chapter04; make html

Chapter05::
	cd Chapter05; make html

Chapter06::
	cd Chapter06; make html

Chapter07::
	cd Chapter07; make html

Chapter08::
	cd Chapter08; make html

######

compall:
	cd Chapter01; make all
	cd Chapter02; make all
	cd Chapter03; make all
	cd Chapter04; make all
	cd Chapter05; make all
	cd Chapter06; make all
	cd Chapter07; make all
	cd Chapter08; make all

######

updateall:: update01 update02 update03 update04 update05 update06 update07 update08

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

