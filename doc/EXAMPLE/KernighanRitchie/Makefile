######

all:: \
  Chapter01 Chapter02 Chapter03 Chapter04 Chapter05 Chapter06 Chapter07 Chapter08 \
  cleanall

######

Chapter01::
	cd Chapter01; make html
	scp Chapter01/*.c Chapter01/*.dats Chapter01/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter01
	cd Chapter01; make cleanall

Chapter02::
	cd Chapter02; make html
	scp Chapter02/*.dats Chapter02/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter02
	cd Chapter02; make cleanall

Chapter03::
	cd Chapter03; make html
	scp Chapter03/*.c Chapter03/*.dats Chapter03/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter03
	cd Chapter03; make cleanall

Chapter04::
	cd Chapter04; make html
	scp Chapter04/*.dats Chapter04/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter04
	cd Chapter04; make cleanall

Chapter05::
	cd Chapter05; make html
	scp Chapter05/*.dats Chapter05/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter05
	cd Chapter05; make cleanall

Chapter06::
	cd Chapter06; make html
	scp Chapter06/*.dats Chapter06/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter06
	cd Chapter06; make cleanall

Chapter07::
	cd Chapter07; make html
	scp Chapter07/*.dats Chapter07/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter07
	cd Chapter07; make cleanall

Chapter08::
	cd Chapter08; make html
	scp Chapter08/*.dats Chapter08/*_dats.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/KernighanRitchie/Chapter08
	cd Chapter08; make cleanall

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

