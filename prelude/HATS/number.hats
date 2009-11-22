(*
**
** An interface for various common funtion on numbers
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Shivkumar Chandrasekaran (shiv AT ece DOT ucsb DOT edu)
**
** Time: Summer, 2009
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

staload "prelude/SATS/number.sats"

(* ****** ****** *)

implement print_typ<float> () = print "float"
implement print_typ<double> () = print "double"
implement print_typ<ccmplx> () = print "ccmplx"
implement print_typ<zcmplx> () = print "zcmplx"

(* ****** ****** *)

implement print_elt<float> (x) = print_float x
implement print_elt<double> (x) = print_double x
implement print_elt<ccmplx> (x) = print_ccmplx x
implement print_elt<zcmplx> (x) = print_zcmplx x

(* ****** ****** *)

implement of_int<float> (x) = float_of_int (x)
implement of_int<double> (x) = double_of_int x
implement of_int<ccmplx> (x) = ccmplx_of_int (x)
implement of_int<zcmplx> (x) = zcmplx_of_int (x)

(* ****** ****** *)

implement of_double<float> (x) = float_of_double (x)
implement of_double<double> (x) = x
implement of_double<ccmplx> (x) = ccmplx_of_float (float_of_double x)
implement of_double<zcmplx> (x) = zcmplx_of_double (x)

(* ****** ****** *)

implement abs<float,float> (x) = abs_float (x)
implement abs<double,double> (x) = abs_double (x)
implement abs<ccmplx,float> (x) = abs_ccmplx (x)
implement abs<zcmplx,double> (x) = abs_zcmplx (x)

(* ****** ****** *)

implement neg<float> (x) = neg_float (x)
implement neg<double> (x) = neg_double (x)
implement neg<ccmplx> (x) = neg_ccmplx (x)
implement neg<zcmplx> (x) = neg_zcmplx (x)

(* ****** ****** *)

implement add<float> (x1, x2) = add_float_float (x1, x2)
implement add<double> (x1, x2) = add_double_double (x1, x2)
implement add<ccmplx> (x1, x2) = add_ccmplx_ccmplx (x1, x2)
implement add<zcmplx> (x1, x2) = add_zcmplx_zcmplx (x1, x2)

implement sub<float> (x1, x2) = sub_float_float (x1, x2)
implement sub<double> (x1, x2) = sub_double_double (x1, x2)
implement sub<ccmplx> (x1, x2) = sub_ccmplx_ccmplx (x1, x2)
implement sub<zcmplx> (x1, x2) = sub_zcmplx_zcmplx (x1, x2)

implement mul<float> (x1, x2) = mul_float_float (x1, x2)
implement mul<double> (x1, x2) = mul_double_double (x1, x2)
implement mul<ccmplx> (x1, x2) = mul_ccmplx_ccmplx (x1, x2)
implement mul<zcmplx> (x1, x2) = mul_zcmplx_zcmplx (x1, x2)

implement div<float> (x1, x2) = div_float_float (x1, x2)
implement div<double> (x1, x2) = div_double_double (x1, x2)
implement div<ccmplx> (x1, x2) = div_ccmplx_ccmplx (x1, x2)
implement div<zcmplx> (x1, x2) = div_zcmplx_zcmplx (x1, x2)

(* ****** ****** *)

implement scal<float,float> (x1, x2) = mul_float_float (x1, x2)
implement scal<float,ccmplx> (x1, x2) = let
  val x2_r = ccmplx_real (x2) and x2_i = ccmplx_imag (x2) in
  ccmplx_make_cart (mul_float_float (x1, x2_r), mul_float_float (x1, x2_i))
end // end of ...
implement scal<ccmplx,ccmplx> (x1, x2) = mul_ccmplx_ccmplx (x1, x2)

implement scal<double,double> (x1, x2) = mul_double_double (x1, x2)
implement scal<double,zcmplx> (x1, x2) = let
  val x2_r = zcmplx_real (x2) and x2_i = zcmplx_imag (x2) in
  zcmplx_make_cart (mul_double_double (x1, x2_r), mul_double_double (x1, x2_i))
end // end of ...
implement scal<zcmplx,zcmplx> (x1, x2) = mul_zcmplx_zcmplx (x1, x2)

(* ****** ****** *)

implement eq<float> (x1, x2) = eq_float_float (x1, x2)
implement eq<double> (x1, x2) = eq_double_double (x1, x2)
implement eq<ccmplx> (x1, x2) = eq_ccmplx_ccmplx (x1, x2)
implement eq<zcmplx> (x1, x2) = eq_zcmplx_zcmplx (x1, x2)

implement neq<float> (x1, x2) = neq_float_float (x1, x2) 
implement neq<double> (x1, x2) = neq_double_double (x1, x2)
implement neq<ccmplx> (x1, x2) = neq_ccmplx_ccmplx (x1, x2)
implement neq<zcmplx> (x1, x2) = neq_zcmplx_zcmplx (x1, x2)

(* ****** ****** *)

(* end of [number.hats] *)
