#########################################################################
##                                                                     ##
##                         Applied Type System                         ##
##                                                                     ##
##                              Hongwei Xi                             ##
##                                                                     ##
#########################################################################

##
## ATS/Anairiats - Unleashing the Potential of Types!
##
## Copyright (C) 2002-2010 Hongwei Xi.
##
## ATS is  free software;  you can redistribute it and/or modify it under
## the  terms of the  GNU General Public License as published by the Free
## Software Foundation; either version 2.1, or (at your option) any later
## version.
##
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
##
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
## Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
## 02110-1301, USA.
##

######

##
## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Author: Likai Liu (liulk AT cs DOT bu DOT edu)
## Author: Yuri D'Elia (wavexx AT thregr DOT org)
##

# Disable parallelism and implicit rules
MAKEFLAGS += -j1
.SUFFIXES:

all:: Makefile

######

# integration with autoconf.

SRC_CONFIG_FILES := config.mk.in config.h.in
BUILT_CONFIG_FILES := $(SRC_CONFIG_FILES:%.in=%)

Makefile: config.mk

config.status: configure
	./configure
	touch $@

$(BUILT_CONFIG_FILES): %: config.status $(filter-out %,$(SRC_CONFIG_FILES))
	./config.status
	touch $(BUILT_CONFIG_FILES)

config.h.in: configure.ac
	autoheader $<
	touch $@

configure: configure.ac $(SRC_CONFIG_FILES)
	aclocal
	automake --add-missing --foreign || true
	autoconf
	touch $(BUILT_CONFIG_FILES)

-include config.mk

######

DESTDIR :=

export ATSHOME
export ATSHOMERELOC
export ATSHOMEQ

######

ATSHOMEBIN = $(ATSHOMEQ)/bin

######

install:: config.h
#
# recursively install all files in the list except .svn control files.
#
	for d in ccomp/runtime contrib doc libats libc prelude; do \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -d $(DESTDIR)$(ATSNEWHOME)/"$$d" && \
	  find "$$d" -name .svn -prune -o -type f \
            -exec $(INSTALL) -m 644 -D \{} $(DESTDIR)$(ATSNEWHOME)/\{} \; \
	    -print && \
	  find "$$d" -name .svn -prune -o -type l \
            -exec cp -d \{} $(DESTDIR)$(ATSNEWHOME)/\{} \; \
	    -print; \
	done
#
# install specific files in the list as regular files.
#
	for f in \
	    COPYING INSTALL *.txt ccomp/lib/*.a ccomp/lib64/*.a config.h; \
	do \
	  [ -f "$$f" ] || continue; \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -m 644 -D "$$f" $(DESTDIR)$(ATSNEWHOME)/"$$f" && \
	  echo "$$f"; \
	done

	# install specific files in the list as executables.
	for f in bin/*; do \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -m 755 -D "$$f" $(DESTDIR)$(ATSNEWHOME)/"$$f" && \
	  echo "$$f"; \
	done
#
# install multiple copies of wrapper script, for each binary.
#
	for f in bin/*; do \
	  b=`basename "$$f"`; \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -m 755 -D ats_env.sh $(DESTDIR)$(bindir)/"$$b" && \
	  echo install ats_env.sh to $(bindir)/"$$b"; \
	done

######

test::
	sh test.sh

######

all:: all-anairiats

#
# HX: [all1] is the entry point for bootstrapping with ATS/Geizella
#
all-geizella:: atsopt0-geizella
all-geizella::all1

#
# HX: [all1] is the entry point for bootstrapping with ATS/Anairiats
#
all-anairiats:: atsopt0-anairiats
all-anairiats:: all1

######

all1:: bootstrapping
all1:: atsopt1
all1:: bin/atscc
all1:: bin/atslib
all1:: libfiles
all1:: libfiles_mt
all1:: libatsdoca
all1:: bin/atspack
all1:: ccomp/runtime/GCATS/gc.o
all1:: ccomp/runtime/GCATS/gc_mt.o
# atsdoc and atslex may require GC
all1:: atsopt1_gc
all1:: bin/atslex
all1:: bin/atsdoc
all1:: contrib
all1:: ; @echo "ATS/Anairiats has been built up successfully!"
all1:: ; @echo "The value of ATSHOME for this build is \"$(ATSHOME)\"."
all1:: ; @echo "The value of ATSHOMERELOC for this build is \"$(ATSHOMERELOC)\"."

###### w/o GC ######

atsopt0:: atsopt0-anairiats

#
# bootstrapping via ocaml
#
atsopt0-geizella: ; $(MAKE) -C bootstrap0 -f ./Makefile atsopt

#
# bootstrapping via gcc
#
atsopt0-anairiats: ; $(MAKE) -C bootstrap0 -f ./Makefile atsopt

###### bootstrapping ######

bootstrapping:: ; $(MAKE) -C src -f ./Makefile_srcbootstrap all

###### w/o GC ######

atsopt1:: ; $(MAKE) -C bootstrap1 -f ../Makefile_bootstrap atsopt
atsopt1:: ; $(CPF) bootstrap1/atsopt $(ATSHOMEBIN)/atsopt

###### with GC ######

atsopt1_gc:: ; $(MAKE) -C bootstrap1 -f ../Makefile_bootstrap atsopt_gc
atsopt1_gc:: ; $(CPF) bootstrap1/atsopt_gc $(ATSHOMEBIN)/atsopt

###### contrib libraries ######

contrib::
ifeq (1,1)
	$(MAKE) -C contrib/parcomb all
endif
ifeq ($(HAVE_LIBGLIB20),1)
	$(MAKE) -C contrib/glib all
endif
ifeq ($(HAVE_LIBGTK20),1)
	$(MAKE) -C contrib/cairo all
	$(MAKE) -C contrib/pango all
	$(MAKE) -C contrib/GTK all
endif
ifeq ($(HAVE_LIBSDL10),1)
	$(MAKE) -C contrib/SDL all
endif

###### some toplevel commands ######

bin/atscc bin/atslib:
	$(MAKE) -C utils/scripts atscc
	$(CPF) utils/scripts/atscc $(ATSHOMEBIN)
	$(MAKE) -C utils/scripts atslib
	$(CPF) utils/scripts/atslib $(ATSHOMEBIN)
	$(MAKE) -C utils/scripts clean

bin/atspack:
	$(MAKE) -C utils/scripts atspack
	$(CPF) utils/scripts/atspack $(ATSHOMEBIN)

bin/atsdoc:
	$(MAKE) -C utils/atsdoc atsdoc
	$(CPF) utils/atsdoc/atsdoc $(ATSHOMEBIN)

###### library ######

ATS_PROOFCHECK=
# ATS_PROOFCHECK=-D_ATS_PROOFCHECK # it should be turned on from time to time

#
# [CC -E] for preprocessing
#

ATSLIB=$(ATSHOMEBIN)/atslib

.libfiles_local: .libfiles ; $(CC) -E -P -x c -o $@ $<
libfiles: .libfiles_local
	$(ATSLIB) $(ATS_PROOFCHECK) -O2 --libats
	$(ATSLIB) $(ATS_PROOFCHECK) -O2 --libats_lex
	$(ATSLIB) $(ATS_PROOFCHECK) -O2 --libats_smlbas

lib32files: .libfiles_local
	$(ATSLIB) $(ATS_PROOFCHECK) -m32 -O2 --libats
	$(ATSLIB) $(ATS_PROOFCHECK) -m32 -O2 --libats_lex
	$(ATSLIB) $(ATS_PROOFCHECK) -m32 -O2 --libats_smlbas

lib64files: .libfiles_local
	$(ATSLIB) $(ATS_PROOFCHECK) -m64 -O2 --libats
	$(ATSLIB) $(ATS_PROOFCHECK) -m64 -O2 --libats_lex
	$(ATSLIB) $(ATS_PROOFCHECK) -m64 -O2 --libats_smlbas

.libfiles_mt_local: .libfiles_mt ; $(CC) -E -P -x c -o $@ $<
libfiles_mt: .libfiles_mt_local
	$(ATSLIB) $(ATS_PROOFCHECK) -O2 -D_ATS_MULTITHREAD --libats_mt

libatsdoca: ; $(MAKE) -C libatsdoc

###### a lexer for ATS ######

bin/atslex:
	$(MAKE) -C utils/atslex atslex
	$(CPF) utils/atslex/atslex $(ATSHOMEBIN)
	$(MAKE) -C utils/atslex atslex clean

###### GC runtime ######

ccomp/runtime/GCATS/gc.o:
	$(MAKE) -C ccomp/runtime/GCATS gc.o
	$(MAKE) -C ccomp/runtime/GCATS clean

ccomp/runtime/GCATS/gc_mt.o:
	$(MAKE) -C ccomp/runtime/GCATS gc_mt.o
	$(MAKE) -C ccomp/runtime/GCATS clean

######

package::
	bin/atspack --source

precompiled::
	bin/atspack --precompiled
	rm -fr usr/share/atshome
	mv ats-lang-anairiats-* usr/share/atshome
	tar -zvcf ats-lang-anairiats-precompiled.tar.gz \
          --exclude=usr/.svn --exclude=usr/bin/.svn --exclude=usr/share/.svn usr/

######

srclines::
	$(MAKE) -C src lines

liblines::
	wc -l \
          prelude/*/*.?ats \
          prelude/*/*/*.?ats \
          libc/*/*.?ats \
          libc/*/*/*.?ats \
          libats/*/*.?ats \
          libats/*/*/*.?ats \

######

CPF=cp -f
RMF=rm -f

######

clean::
	$(RMF) bootstrap0/*.o
	$(RMF) bootstrap1/*.c
	$(RMF) bootstrap1/*.h
	$(RMF) bootstrap1/*.cats
	$(RMF) bootstrap1/*.o

cleanall:: clean
	$(RMF) $(BUILT_CONFIG_FILES)
	$(RMF) .libfiles_local
	$(RMF) .libfiles_mt_local
	$(RMF) bootstrap0/atsopt
	$(RMF) bootstrap1/atsopt
	$(RMF) src/ats_grammar_yats.c src/ats_grammar_yats.h
	$(RMF) bin/atsopt
	$(RMF) bin/atscc bin/atslib bin/atslex bin/atspack
	$(RMF) bin/atsdoc
	$(RMF) libatsdoc/libatsdoc.a
	$(RMF) ccomp/lib/libats.a
	$(RMF) ccomp/lib/libats_mt.a
	$(RMF) ccomp/lib/libats_lex.a
	$(RMF) ccomp/lib/libats_smlbas.a
	$(RMF) ccomp/lib/output/*
	$(RMF) ccomp/lib64/libats.a
	$(RMF) ccomp/lib64/libats_mt.a
	$(RMF) ccomp/lib64/libats_lex.a
	$(RMF) ccomp/lib64/libats_smlbas.a
	$(RMF) ccomp/lib64/output/*
	$(RMF) contrib/glib/atsctrb_glib.o
	$(RMF) contrib/cairo/atsctrb_cairo.o
	$(RMF) contrib/pango/atsctrb_pango.o
	$(RMF) contrib/X11/atsctrb_X11.o
	$(RMF) contrib/GTK/atsctrb_GTK.o
	$(RMF) contrib/GL/atsctrb_GL.o
	$(RMF) contrib/GL/atsctrb_glut.o
	$(RMF) contrib/gtkglext/atsctrb_gtkglext.o
	$(RMF) contrib/SDL/atsctrb_SDL.o

cleanall:: ; $(MAKE) -C utils/atslex -f ./Makefile cleanall
cleanall:: ; $(MAKE) -C utils/scripts -f ./Makefile cleanall
cleanall:: ; $(MAKE) -C ccomp/runtime/GCATS -f ./Makefile cleanall

distclean:: cleanall
distclean:: ; find . -name .svn -prune -o -name \*~ -exec rm \{} \;

###### end of [Makefile] ######
