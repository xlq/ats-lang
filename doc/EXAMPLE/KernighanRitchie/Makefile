#
#
# Makefile for some K&R examples
#
#

######

.PHONY: all
all: checkall

######

checkall:: ; make -C Chapter01 checkall
checkall:: ; make -C Chapter02 checkall
checkall:: ; make -C Chapter03 checkall
checkall:: ; make -C Chapter04 checkall
checkall:: ; make -C Chapter05 checkall
checkall:: ; make -C Chapter06 checkall
checkall:: ; make -C Chapter07 checkall
checkall:: ; make -C Chapter08 checkall

######

compall:: ; make -C Chapter01 compall
compall:: ; make -C Chapter02 compall
compall:: ; make -C Chapter03 compall
compall:: ; make -C Chapter04 compall
compall:: ; make -C Chapter05 compall
compall:: ; make -C Chapter06 compall
compall:: ; make -C Chapter07 compall
compall:: ; make -C Chapter08 compall

######

html:: ; make -C Chapter01 html
html:: ; make -C Chapter02 html
html:: ; make -C Chapter03 html
html:: ; make -C Chapter04 html
html:: ; make -C Chapter05 html
html:: ; make -C Chapter06 html
html:: ; make -C Chapter07 html
html:: ; make -C Chapter08 html  

######

update:: update01
update01:: ; scp Chapter01/*.dats Chapter01/*_dats.html \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter01

update:: update02
update02:: ; scp Chapter02/*.dats Chapter02/*_dats.html \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter02

update:: update03
update03:: ; scp Chapter03/*.dats Chapter03/*_dats.html \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter03

update:: update04
update04:: ; scp Chapter04/*.dats Chapter04/*_dats.html \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter04

update:: update05
update05:: ; scp Chapter05/*.dats Chapter05/*_dats.html \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter05

update:: update06
update06:: ; scp Chapter06/*.dats Chapter06/*_dats.html \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter06

update:: update07
update07:: ; scp Chapter07/*.dats Chapter07/*_dats.html \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter07

update:: update08
update08:: ; scp Chapter08/*.dats Chapter08/*_dats.html \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter08

######

cleanall:: ; make -C  Chapter01 cleanall
cleanall:: ; make -C  Chapter02 cleanall
cleanall:: ; make -C  Chapter03 cleanall
cleanall:: ; make -C  Chapter04 cleanall
cleanall:: ; make -C  Chapter05 cleanall
cleanall:: ; make -C  Chapter06 cleanall
cleanall:: ; make -C  Chapter07 cleanall
cleanall:: ; make -C  Chapter08 cleanall

###### end of [Makefile] ######
