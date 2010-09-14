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
## Copyright (C) 2002-2008 Hongwei Xi.
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

######

install:: config.h
	# recursively install all files in the list except .svn control files.
	for d in ccomp/runtime contrib doc libats libc prelude; do \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -d $(DESTDIR)$(ATSNEWHOME)/"$$d" && \
	  find "$$d" -name .svn -prune -o -type f \
            -exec $(INSTALL) -m 644 -D \{} $(DESTDIR)$(ATSNEWHOME)/\{} \; \
	    -print; \
	done

	# install specific files in the list as regular files.
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

	# install multiple copies of wrapper script, for each binary.
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
# HX: [all1] is the entry point for bootstrapping with ATS/Anairiats
#
all-anairiats:: \
  atsopt0-anairiats all1

#
# HX: [all1] is the entry point for bootstrapping with ATS/Geizella
#
all-geizella:: \
  atsopt0-geizella all1

all1:: \
  bootstrapping \
  atsopt1 \
  bin/atscc \
  bin/atslib \
  libfiles libfiles_mt \
  bin/atspack \
  bin/atslex \
  ccomp/runtime/GCATS/gc.o \
  ccomp/runtime/GCATS/gc_mt.o \
  atsopt1_gc \
  contrib
	@echo "ATS/Anairiats has been built up successfully!"
	@echo "The value of ATSHOME for this build is \"$(ATSHOME)\"."
	@echo "The value of ATSHOMERELOC for this build is \"$(ATSHOMERELOC)\"."

###### w/o GC ######

atsopt0:: atsopt0-anairiats

atsopt0-anairiats::
	$(MAKE) -C bootstrap0 -f ../Makefile_bootstrap BOOTSTRAP0=1 atsopt

atsopt0-geizella::
	$(MAKE) -C bootstrap0 -f ./Makefile atsopt

###### bootstrapping ######

bootstrapping:: ; cd src; $(MAKE) -f ./Makefile_srcbootstrap all

###### w/o GC ######

atsopt1::
	$(MAKE) -C bootstrap1 -f ../Makefile_bootstrap BOOTSTRAP1=1 atsopt
	cp bootstrap1/atsopt $(ATSHOME)/bin/atsopt

###### with GC ######

atsopt1_gc::
	$(MAKE) -C bootstrap1 -f ../Makefile_bootstrap BOOTSTRAP1=1 atsopt_gc
	cp bootstrap1/atsopt_gc $(ATSHOME)/bin/atsopt

###### contrib libraries ######

contrib::
ifdef HAVE_LIBGLIB20
	cd contrib/glib; make atsctrb_glib.o; make clean
endif
ifdef HAVE_LIBGTK20
	cd contrib/cairo; make atsctrb_cairo.o; make clean
	cd contrib/pango; make atsctrb_pango.o; make clean
	cd contrib/GTK; make atsctrb_GTK.o; make clean
endif
ifdef HAVE_LIBSDL
	cd contrib/SDL; make atsctrb_SDL.o; make clean
endif

###### some toplevel commands ######

bin/atscc bin/atslib:
	cd utils/scripts; $(MAKE) atscc; cp atscc $(ATSHOME)/bin
	cd utils/scripts; $(MAKE) atslib; cp atslib $(ATSHOME)/bin
	cd utils/scripts; $(MAKE) clean

bin/atspack:
	cd utils/scripts; $(MAKE) atspack; cp atspack $(ATSHOME)/bin

###### library ######

ATS_PROOFCHECK=
# ATS_PROOFCHECK=-D_ATS_PROOFCHECK # it should be turned on from time to time

#
# [CC -E] for preprocessing
#

ATSLIB=$(ATSHOME)/bin/atslib

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
	$(ATSLIB) $(ATS_PROOFCHECK) -D_ATS_MULTITHREAD -O2 --libats_mt

###### a lexer for ATS ######

bin/atslex:
	cd utils/atslex; $(MAKE) atslex; cp atslex $(ATSHOME)/bin
	cd utils/atslex; $(MAKE) clean

###### GC runtime ######

ccomp/runtime/GCATS/gc.o:
	cd ccomp/runtime/GCATS; $(MAKE) gc.o; $(MAKE) clean

ccomp/runtime/GCATS/gc_mt.o:
	cd ccomp/runtime/GCATS; $(MAKE) gc_mt.o; $(MAKE) clean

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
	cd src; make lines

liblines::
	wc -l \
          prelude/*/*.?ats prelude/*/*/*.?ats \
          libc/*/*.?ats libc/*/*/*.?ats \
          libats/*/*.?ats libats/*/*/*.?ats

######

clean::
	rm -f bootstrap0/*.o
	rm -f bootstrap1/*.c bootstrap1/*.o
	$(MAKE) -C utils/atslex -f ./Makefile clean
	$(MAKE) -C utils/scripts -f ./Makefile clean
	cd ccomp/runtime/GCATS; $(MAKE) clean

cleanall:: clean
	rm -f $(BUILT_CONFIG_FILES)
	rm -f .libfiles_local
	rm -f .libfiles_mt_local
	rm -f bootstrap0/atsopt
	rm -f bootstrap1/atsopt
	rm -f bin/atsopt bin/atscc bin/atslib bin/atslex bin/atspack
	rm -f ccomp/lib/libats.a
	rm -f ccomp/lib/libats_mt.a
	rm -f ccomp/lib/libats_lex.a
	rm -f ccomp/lib/libats_smlbas.a
	rm -f ccomp/lib/output/*
	rm -f ccomp/lib64/libats.a
	rm -f ccomp/lib64/libats_mt.a
	rm -f ccomp/lib64/libats_lex.a
	rm -f ccomp/lib64/libats_smlbas.a
	rm -f ccomp/lib64/output/*
	$(MAKE) -C ccomp/runtime/GCATS -f ./Makefile cleanall
	rm -f contrib/glib/atsctrb_glib.o
	rm -f contrib/cairo/atsctrb_cairo.o
	rm -f contrib/pango/atsctrb_pango.o
	rm -f contrib/X11/atsctrb_X11.o
	rm -f contrib/GTK/atsctrb_GTK.o
	rm -f contrib/GL/atsctrb_GL.o
	rm -f contrib/SDL/atsctrb_SDL.o
	find . -name .svn -prune -o -name \*~ -exec rm \{} \;

######
#
# end of [Makefile]
#
######
