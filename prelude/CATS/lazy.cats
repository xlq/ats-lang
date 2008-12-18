/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/*                              Hongwei Xi                             */
/*                                                                     */
/***********************************************************************/

/*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
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
**
*/

/* ****** ****** */

// author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

/* ****** ****** */

#ifndef ATS_PRELUDE_LAZY_CATS
#define ATS_PRELUDE_LAZY_CATS

/* ****** ****** */

typedef struct {
  ats_ptr_type tag ; ats_clo_ptr_type data ;
} thunkvalue_struct ;

/* ****** ****** */

#define ats_instr_move_lazy_delay_mac(tmp, hit, vp_clo) do { \
  tmp = ATS_MALLOC ( \
    sizeof(ats_ptr_type) + (sizeof(hit) <= sizeof(ats_ptr_type) ? sizeof(ats_ptr_type) : sizeof(hit)) \
  ) ; /* end of [ATS_MALLOC] */ \
  ((thunkvalue_struct*)tmp)->tag = (ats_ptr_type)0 ; ((thunkvalue_struct*)tmp)->data = (vp_clo) ; \
} while (0) /* end of [do ... while ...] */

#define ats_instr_move_lazy_vt_delay_mac(tmp, hit, vp_clo) \
  do { tmp = (vp_clo) ; } while (0) /* end of [do ... while ...] */

#define ats_instr_move_lazy_force_mac(tmp, hit, vp_lazy) do { \
  if (((thunkvalue_struct*)vp_lazy)->tag == 0) { \
    tmp = ((hit (*)(ats_clo_ptr_type))ats_closure_fun(((thunkvalue_struct*)vp_lazy)->data))(((thunkvalue_struct*)vp_lazy)->data) ; \
    ((thunkvalue_struct*)vp_lazy)->tag += 1 ; \
    *(hit*)(&((thunkvalue_struct*)vp_lazy)->data) = tmp ; \
  } else { \
    tmp = *(hit*)(&((thunkvalue_struct*)vp_lazy)->data) ; \
  } /* end of [if] */ \
} while (0) /* end of [do ... while ...] */

#define ats_instr_move_lazy_vt_force_mac(tmp, hit, vp_lazy) do { \
  tmp = ((hit (*)(ats_clo_ptr_type))ats_closure_fun(vp_lazy))(vp_lazy) ; ATS_FREE (vp_lazy) ; \
} while (0) /* end of [do ... while ...] */

/* ****** ****** */

#endif /* ATS_PRELUDE_LAZY_CATS */

/* end of [lazy.cats] */
