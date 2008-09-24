%{^

#include "libc/CATS/stdio.cats"

%}

staload "libc/SATS/stdio.sats"

#define i2c char_of_int

fn fcopy (fil_s: &FILE r, fil_d: &FILE w): void = let
  fun loop (fil_s: &FILE r, fil_d: &FILE w): void =
    let val c = fgetc (file_mode_lte_r_r | fil_s) in
      if c >= 0 then begin
        fputc (file_mode_lte_w_w | i2c c, fil_d); loop (fil_s, fil_d)
      end
    end
in
  loop (fil_s, fil_d)
end // end of [fcopy]

(* ****** ****** *)

// a simple test

implement main (argc, argv) = let

val cmd = argv.[0]
val () = if (argc < 2) then
  exit_prerrf {void} (1, "Usage: %s [src] or %s [src] [dst]\n", @(cmd, cmd))
val () = assert (argc >= 2)

in

if argc > 2 then let
  val (pf_s | ptr_s) = fopen (argv.[1], #mode="r")
  val (pf_d | ptr_d) = fopen (argv.[2], #mode="w")
in
  fcopy (!ptr_s, !ptr_d);
  fclose (pf_s | ptr_s);
  fclose (pf_d | ptr_d)
end else let
  val (pf_s | ptr_s) = fopen (argv.[1], #mode="r")
  val (pf_d | ptr_d) = stdout_get ()
in
  fcopy (!ptr_s, !ptr_d);
  fclose (pf_s | ptr_s);
  stdout_view_set (pf_d | (*none*))
end // end of [if]

end // end of [main]

(* ****** ****** *)

(* end of [input-and-output.dats] *)
