/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
**
** ATS is  free software;  you can redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef ATS_LIBC_TIME_CATS
#define ATS_LIBC_TIME_CATS

/* ****** ****** */

#include <time.h>

/* ****** ****** */

#include "ats_types.h"

typedef struct tm ats_tm_struct_type ;

/* ****** ****** */

#include "libc/sys/CATS/types.cats"

/* ****** ****** */

ATSinline()
ats_lint_type
atslib_lint_of_time (time_t t) { return t ; }

ATSinline()
ats_double_type
atslib_double_of_time (time_t t) { return t ; }

/* ****** ****** */

ATSinline()
ats_int_type atslib_tm_sec_get (ats_ptr_type tm) {
  return ((struct tm *)tm)->tm_sec ;
}

ATSinline()
ats_int_type atslib_tm_min_get (ats_ptr_type tm) {
  return ((struct tm *)tm)->tm_min ;
}

ATSinline()
ats_int_type atslib_tm_hour_get (ats_ptr_type tm) {
  return ((struct tm *)tm)->tm_hour ;
}

ATSinline()
ats_int_type atslib_tm_mday_get (ats_ptr_type tm) {
  return ((struct tm *)tm)->tm_mday ;
}

ATSinline()
ats_int_type atslib_tm_mon_get (ats_ptr_type tm) {
  return ((struct tm *)tm)->tm_mon ;
}

ATSinline()
ats_int_type atslib_tm_year_get (ats_ptr_type tm) {
  return ((struct tm *)tm)->tm_year ;
}

ATSinline()
ats_int_type atslib_tm_wday_get (ats_ptr_type tm) {
  return ((struct tm *)tm)->tm_wday ;
}

ATSinline()
ats_int_type atslib_tm_yday_get (ats_ptr_type tm) {
  return ((struct tm *)tm)->tm_yday ;
}

ATSinline()
ats_int_type atslib_tm_isdst_get (ats_ptr_type tm) {
  return ((struct tm *)tm)->tm_isdst ;
}

//

/* ****** ****** */

ATSinline()
ats_time_type
atslib_time_get () { return time((time_t*)0) ; }

ATSinline()
ats_time_type
atslib_time_get_and_set
  (ats_ref_type p) { return time((time_t*)p) ; }
// end of [atslib_time_get_and_set]

/* ****** ****** */

#define atslib_difftime difftime

/* ****** ****** */

#define atslib_ctime ctime
#define atslib_ctime_r ctime_r

/* ****** ****** */

#define atslib_localtime localtime
#define atslib_localtime_r localtime_r

/* ****** ****** */

#define atslib_strftime strftime

/* ****** ****** */

ATSinline()
ats_lint_type
atslib_lint_of_clock (clock_t t) { return t ; }

ATSinline()
ats_double_type
atslib_double_of_clock (clock_t t) { return t ; }

/* ****** ****** */

ATSinline()
ats_clock_type
atslib_clock (void) { return clock (); }

/* ****** ****** */

#endif /* ATS_LIBC_TIME_CATS */

/* end of [time.cats] */
