//
// LazyFoo-lesson01 translated into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson01
//

(* ****** ****** *)

staload "contrib/SDL/SATS/SDL.sats"

(* ****** ****** *)

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  // Set up screen
  val screen = SDL_SetVideoMode_exn (640, 480, 32, SDL_SWSURFACE)
  // loading a bitmap file
  val bmpfil = SDL_LoadBMP_exn ("LazyFoo-lesson01/hello.bmp")
  // SDL_UpperBlit_ptr is "unsafe" SDL_UpperBlit
  val _err = SDL_UpperBlit_ptr (bmpfil, null, screen, null)
  val _err = SDL_Flip (screen)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val _err = SDL_Delay ((Uint32)2000(*ms*))
  val () = SDL_FreeSurface (bmpfil)
  // [SDL_Quit_screen] is a no-op cast
  val _ptr = SDL_Quit_screen (screen) // [screen] should be freed by SDL_Quit
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson01.dats] *)
