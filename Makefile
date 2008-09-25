#########################################################################
#                                                                       #
#                         Applied Type System                           #
#                                                                       #
#                              Hongwei Xi                               #
#                                                                       #
#########################################################################

#
#  ATS/Anairiats - Unleashing the Potential of Types!
#
#  Copyright (C) 2002-2008 Hongwei Xi.
#
#  ATS is  free software;  you can redistribute it and/or modify it under
#  the  terms of the  GNU General Public License as published by the Free
#  Software Foundation; either version 2.1, or (at your option) any later
#  version.
# 
#  ATS is distributed in the hope that it will be useful, but WITHOUT ANY
#  WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
#  FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
#  for more details.
# 
#  You  should  have  received  a  copy of the GNU General Public License
#  along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
#  Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
#  02110-1301, USA.
#

#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#

######

GCC=gcc

PWD=$(shell pwd)
ifdef ATSHOME
  ATSHOMEDEF=1
else
  ATSHOMEDEF=0
  export ATSHOME=$(PWD)
endif

######

all: \
  atscheck \
  config.h \
  atsopt0 \
  bin/atscc \
  bin/atslib \
  libfiles \
  bin/atslex \
  bootstrapping \
  atsopt1 \
  ccomp/runtime/GCATS/gc.o \
  atsopt1_gc
	echo "ATS/Anairiats has been built up successfully!"
	echo "The value of ATSHOME for this build is \"$(ATSHOME)\"."

###### system configuration ######

atscheck:
	echo "$(ATSHOME)" > .ATSHOME
ifeq ($(ATSHOMEDEF),1)
	/bin/bash -r ./atshomecheck.sh
endif
ifdef ATSHOMERELOC
	echo "$(ATSHOMERELOC)" > .ATSHOMERELOC
endif

config.h: configure ; ./configure

###### bootstrap/Makefile ######

bootstrap0/Makefile:
	$(GCC) -E -x c .bootstrap_header | cat - .bootstrap_makefile > bootstrap0/Makefile

bootstrap1/Makefile:
	$(GCC) -E -x c .bootstrap_header | cat - .bootstrap_makefile > bootstrap1/Makefile

###### w/o GC ######
atsopt0: bootstrap0/Makefile; cd bootstrap0; make atsopt; mv atsopt "$(ATSHOME)"/bin

###### bootstrapping ######
bootstrapping: ; cd src; make atsopt0; make -f Makefile_bootstrap all

###### w/o GC ######
atsopt1: bootstrap1/Makefile; cd bootstrap1; make atsopt; mv atsopt "$(ATSHOME)"/bin

###### w/o GC ######
atsopt1_gc: bootstrap1/Makefile; cd bootstrap1; make atsopt_gc; mv atsopt "$(ATSHOME)"/bin

###### some toplevel commands ######
bin/atscc bin/atslib:
	cd utils/scripts; make atscc; mv atscc "$(ATSHOME)"/bin
	cd utils/scripts; make atslib; mv atslib "$(ATSHOME)"/bin
	cd utils/scripts; make clean

###### library ######

# [gcc -E] for preprocessing
.libfiles_local: ; $(GCC) -E -P -x c .libfiles -o .libfiles_local
libfiles: .libfiles_local; "$(ATSHOME)"/bin/atslib -all

###### a lexer for ATS ######
bin/atslex:
	cd utils/atslex; make atslex; mv atslex "$(ATSHOME)"/bin
	cd utils/atslex; make clean

###### GC runtime ######

ccomp/runtime/GCATS/gc.o:
	cd ccomp/runtime/GCATS; make gc.o; make clean

######

clean::
	rm -f bootstrap0/*.o
	rm -f bootstrap1/*.o
	cd utils/scripts; make clean
	cd utils/atslex; make clean
	cd ccomp/runtime/GCATS; make clean

# The inclusion of [ats_grammar_yats.c] and [ats_grammar_yats.h]
# obviates the need for [yacc] or [byacc]
tar:: cleanall
	rm -rf ATS/*
	cp COPYING ATS
	cp INSTALL ATS
	cp Makefile ATS
	cp Makefile_chmod ATS
	cp .libfiles ATS
	cp configure.ac configure config.h.in ATS
	mkdir ATS/bin
	mkdir ATS/bootstrap
	cp bootstrap/Makefile ATS/bootstrap
	cp bootstrap/*.h ATS/bootstrap
	cp bootstrap/*.cats ATS/bootstrap
	cp bootstrap/*_?ats.c ATS/bootstrap
	mkdir ATS/ccomp
	mkdir ATS/ccomp/runtime
	cp -r ccomp/runtime/*.{c,h} ATS/ccomp/runtime
	mkdir ATS/ccomp/runtime/GCATS
	cp -r ccomp/runtime/GCATS/gc.h ATS/ccomp/runtime/GCATS
	cp -r ccomp/runtime/GCATS/*.?ats ATS/ccomp/runtime/GCATS
	cp -r ccomp/runtime/GCATS/Makefile ATS/ccomp/runtime/GCATS
	cp -r ccomp/runtime/GCATS/README ATS/ccomp/runtime/GCATS
	cp -r ccomp/runtime/GCATS/BUGS.txt ATS/ccomp/runtime/GCATS
	mkdir ATS/ccomp/lib
	mkdir ATS/ccomp/lib/output
	cp -r prelude libc libats ATS
	cp -r utils ATS
	mkdir ATS/src
	cp src/Makefile ATS/src
	cp src/Makefile_bootstrap ATS/src
	cp src/Makefile_typecheck ATS/src
	cp src/*.?ats ATS/src
	cp src/ats_grammar_yats.h ATS/src
	cp src/ats_grammar_yats.c ATS/src
	mkdir ATS/doc
	cp doc/ATS.css doc/ATS.html ATS/doc
	cp doc/FAQ.txt ATS/doc
	cp -r doc/BOOK ATS/doc
	cp -r doc/EXAMPLE ATS/doc
	cp -r doc/IMPLEMENTATION ATS/doc
	cp -r doc/LIBRARY ATS/doc
	cp -r doc/TUTORIAL ATS/doc
	tar -zvcf ATS.tgz ATS/
	mv ATS.tgz ATS
	cp ATS/ATS.tgz /home/fac2/hwxi/public_html/ATS/Anairiats.tgz

cleanall::
	rm -f config.h
	rm -f .libfiles_local
	rm -f bin/atsopt bin/atscc bin/atslib bin/atslex
	rm -f ccomp/lib/libats.a
	rm -f ccomp/lib/libatslex.a
	rm -f ccomp/lib/output/*
	rm -f .*~ *~ */*~ */*/*~ */*/*/*~ */*/*/*/*~
	rm -f bootstrap/Makefile bootstrap/*.o
	cd utils/scripts; make clean
	cd utils/atslex; make clean
	cd ccomp/runtime/GCATS; make cleanall

######
#
# end of [Makefile]
#
######
