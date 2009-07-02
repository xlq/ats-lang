(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
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
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{

#include "libc/CATS/complex.cats"

// ccmplx = ats_fcomplex_type
// zcmplx = ats_dcomplex_type

ats_fcomplex_type
ats_ccmplx_imag_unit = _Complex_I ;

ats_dcomplex_type
ats_zcmplx_imag_unit = _Complex_I ;

// print function

ats_void_type
ats_fprint_ccmplx
  (ats_ptr_type out, ats_fcomplex_type c) {
  int n ;
  float c_i = cimagf(c) ;

  if (c_i >= 0.0) {
    n = fprintf((FILE *)out, "%f+i*%f", crealf(c), c_i) ;
  } else {
    n = fprintf((FILE *)out, "%f-i*%f", crealf(c), -c_i) ;
  }
  return ;
} // end of [ats_fprint_ccmplx]

ats_void_type
ats_fprint_zcmplx
  (ats_ptr_type out, ats_dcomplex_type z) {
  int n ;
  double z_i = cimag(z) ;

  if (z_i >= 0.0) {
    n = fprintf((FILE *)out, "%f+i*%f", creal(z), z_i) ;
  } else {
    n = fprintf((FILE *)out, "%f-i*%f", creal(z), -z_i) ;
  }
  return ;
} // end of [ats_fprint_zcmplx]

%}

(* ****** ****** *)

(* end of [complex.dats] *)

////

(* ****** ****** *)

// implemented in complex.cats

staload M = "math.sats"
staload "complex.sats"

typedef real = double
assume complex = @{ real= real, imag= real }

implement complex_make_cartesian (x, y) =
  @{ real= x, imag= x }

implement complex_make_polar (r, t) =
  @{ real= r * $M.cos t, imag= r * $M.sin t }

//

implement complex_of_double f =  @{ real= f, imag= 0.0 }
implement complex_imag_unit = @{ real= 0.0, imag= 1.0 }

implement complex_real z = z.real
implement complex_imag z = z.imag

(* ****** ****** *)

implement neg_complex z =
  @{ real= ~(z.real), imag= ~(z.imag) }

implement add_complex_complex (z1, z2) =
  @{ real= z1.real + z2.real, imag= z1.imag + z2.imag }

implement sub_complex_complex (z1, z2) =
  @{ real= z1.real - z2.real, imag= z1.imag - z2.imag }

implement mul_complex_complex (z1, z2) = @{
  real= z1.real * z2.real - z1.imag * z2.imag,
  imag= z1.real * z2.imag + z1.imag * z2.real
}

implement div_complex_complex (z1, z2) =
  if abs (z2.real) >= abs (z2.imag) then
    let
       val r = z2.imag / z2.real
       val d = z2.real + r * z2.imag
    in
       @{
          real= (z1.real + r * z1.imag) / d
        , imag= (z1.imag - r * z1.real) / d
        }
    end
  else // abs (z2.real) < abs (z2.imag)
    let
       val r = z2.real / z2.imag
       val d = r * z2.real + z2.imag
    in
       @{
          real= (r * z1.real + z1.imag) / d
        , imag= (r * z1.imag - z1.real) / d
        }
    end

(* ****** ****** *)

implement magnitude_complex z =
  let
     val r = abs (z.real) and i = abs (z.imag)
  in
     if r = 0.0 then i
     else if i = 0.0 then r
     else if r >= i then
       r * sqrt (1.0 + square (i / r))
     else i * sqrt (1.0 + square (r / i))
  end

implement recip_complex z =
  div_complex_complex (complex_one, z)

implement conjugate_complex z = 
  @{ real= z.real, imag= ~(z.imag) }

implement arg_complex z = $M.atan2 (z.imag, z.real)

(* ****** ****** *)

implement square_complex z =
  let
     val r = z.real and i = z.imag
     val rr = r * r
     val ii = i * i
     val ri = r * i
  in
     @{ real= rr - ii, imag= ri + ri }
  end

implement cube_complex z =
  let
     val r = z.real and i = z.imag
     val rr = r * r
     val ii = i * i
  in
     @{ real= r * rr - 3.0 * r * ii, imag= 3.0 * i * rr - i * ii }
  end

implement exp_complex z =
  let val r = $M.exp z.real in
     @{ real= r * $M.cos (z.imag), imag= r * $M.sin (z.imag) }
  end

implement log_complex z =
  @{ real= $M.log (magnitude_complex z) , imag= $M.atan2 (z.imag, z.real) }

implement pow_complex_complex (z1, z2) =
  exp_complex (mul_complex_complex (z2,  log_complex z1))

(* ****** ****** *)
