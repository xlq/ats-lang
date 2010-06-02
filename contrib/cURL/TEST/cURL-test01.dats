(*
**
** A simple cURL example mostly taken from an example by
** chris.double AT double DOT co DOT nz
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: May, 2010
**
*)

(* ****** ****** *)

staload "contrib/cURL/SATS/curl.sats"

implement main () = () where {
  val curl  = curl_easy_init ()
  val () = assert_errmsg (curlptr_isnot_null curl, #LOCATION)
  val (pf_err | err) = curl_easy_setopt (curl, CURLOPT_URL, @("www.ats-lang.org"))
  val () = assert_errmsg (err = CURLE_OK, #LOCATION)
  prval () = curlerr_elim_null (pf_err)
  val (pf_err | err) = curl_easy_perform (curl)
  val () = assert_errmsg (err = CURLE_OK, #LOCATION)
  prval () = curlerr_elim_null (pf_err)
  val () = curl_easy_cleanup (curl)
} // end of [main]

(* ****** ****** *)

(* end of [cURL-test01.dats] *)
