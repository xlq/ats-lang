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
** Copyright (C) 2002-2010 Hongwei Xi.
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

#ifndef ATSCTRB_GLIB_GBASICS_CATS
#define ATSCTRB_GLIB_GBASICS_CATS

/* ****** ****** */

#include "glib/gtypes.h"

/* ****** ****** */

static inline
ats_bool_type
atsctrb_lt_gint_gint
  (gint x, gint y) {
  return (x < y ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_lt_gint_gint]

static inline
ats_bool_type
atsctrb_lte_gint_gint
  (gint x, gint y) {
  return (x <= y ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_lte_gint_gint]

static inline
ats_bool_type
atsctrb_eq_gint_gint
  (gint x, gint y) {
  return (x == y ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_eq_gint_gint]

static inline
ats_bool_type
atsctrb_neq_gint_gint
  (gint x, gint y) {
  return (x != y ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_neq_gint_gint]

/* ****** ****** */

static inline
ats_bool_type
atsctrb_lt_gint32_gint32
  (gint32 x, gint32 y) {
  return (x < y ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_lt_gint32_gint32]

static inline
ats_bool_type
atsctrb_lte_gint32_gint32
  (gint32 x, gint32 y) {
  return (x <= y ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_lte_gint32_gint32]

/* ****** ****** */

static inline
ats_bool_type
atsctrb_lt_guint32_guint32
  (guint32 x, guint32 y) {
  return (x < y ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_lt_guint32_guint32]

static inline
ats_bool_type
atsctrb_lte_guint32_guint32
  (guint32 x, guint32 y) {
  return (x <= y ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_lte_guint32_guint32]

/* ****** ****** */

#endif /* ATSCTRB_GLIB_GBASICS_CATS */
