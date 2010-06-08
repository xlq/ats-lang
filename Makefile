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
##

######

DESTDIR =

# Default target.

export ATSHOMERELOC

.PHONY: all
all:: Makefile_main_temp
	@$(MAKE) -f Makefile_main_temp $@

######

GCC=gcc
Makefile_main_temp:: config.h
	$(GCC) -E -P -x c .makefile_header | cat - Makefile_main > Makefile_main_temp

######

# NOTE(liulk): integration with autoconf.

-include config.mk

config.h ats_env.sh test.sh: \
  config.h.in config.mk.in ats_env.sh.in test.sh.in configure
	test -x config.status && ./config.status || ./configure

Makefile: ;
configure.ac: ;
config.mk.in: ;
ats_env.sh.in: ;
test.sh.in: ;

config.mk:
	touch $@

configure: configure.ac config.h.in
	aclocal
	automake --add-missing --foreign || true
	autoconf

config.h.in: configure.ac; autoheader

# NOTE(liulk): installation to prefix

.PHONY: install
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

.PHONY: test
test::
	sh test.sh

#
# NOTE(liulk): once most major functions of Makefile_main is
# superceded, remove the following code.
#
%: force
	@exec $(MAKE) -f Makefile_main_temp $@
force: ;
