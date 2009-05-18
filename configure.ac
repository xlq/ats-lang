dnl =========================================================================
dnl =                                                                       =
dnl =                         Applied Type System                           =
dnl =                                                                       =
dnl =                              Hongwei Xi                               =
dnl =                                                                       =
dnl =========================================================================

dnl =
dnl =  ATS - Unleashing the Power of Types!
dnl =
dnl =  Copyright (C) 2002-2008 Hongwei Xi.
dnl =
dnl =  ATS is  free software;  you can redistribute it and/or modify it under
dnl =  the  terms of the  GNU General Public License as published by the Free
dnl =  Software Foundation; either version 2.1, or (at your option) any later
dnl =  version.
dnl = 
dnl =  ATS is distributed in the hope that it will be useful, but WITHOUT ANY
dnl =  WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
dnl =  FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
dnl =  for more details.
dnl = 
dnl =  You  should  have  received  a  copy of the GNU General Public License
dnl =  along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
dnl =  Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
dnl =  02110-1301, USA.
dnl =

dnl =
dnl = Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
dnl =

dnl = beg of [configure.ac]

dnl = Autoconf requirements
dnl = AC_INIT(package, version, bug-report-address)
dnl = information on the package
dnl = checks for programs
dnl = checks for libraries
dnl = checks for header files
dnl = checks for types
dnl = checks for structures
dnl = checks for compiler characteristics
dnl = checks for library functions
dnl = checks for system services
dnl = AC_CONFIG_FILES([file...])

AC_INIT([ATS/Anairiats], [version-0.1.4], [hwxi@cs.bu.edu])

AC_CONFIG_SRCDIR([config.h.in])
AC_CONFIG_HEADERS([config.h], [], [])

dnl = check for [gmp.h pcre.h]
AC_CHECK_HEADERS(gmp.h pcre.h)
dnl = check for [GL/gl.h GL/glut.h]
AC_CHECK_HEADERS(GL/gl.h GL/glut.h)

dnl = check for SIZEOF_VOIDP
AC_CHECK_SIZEOF(void*)

dnl = check for some functions
AC_CHECK_FUNCS(posix_memalign memalign)

AC_CONFIG_SUBDIRS([third_party/bdwgc])

# Additional configure arguments for sub-packages.
ac_configure_args="$ac_configure_args --enable-static --disable-shared"
AC_OUTPUT

dnl = end of [configure.ac]
