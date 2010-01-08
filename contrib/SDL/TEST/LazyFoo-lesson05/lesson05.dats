//
// LazyFoo-lesson05 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson05
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: January, 2010
//

(* ****** ****** *)

staload "contrib/SDL/SATS/SDL.sats"

(* ****** ****** *)

#define SCREEN_WIDTH 640
#define SCREEN_HEIGHT 480
#define SCREEN_BPP 32

(* ****** ****** *)

//
// this one is in the SDL_image extension of SDL
//
extern
fun IMG_Load (filename: string): SDL_Surface_ref0 
  = "IMG_Load"

extern
fun load_image (filename: string): SDL_Surface_ref0
implement load_image (filename) = let
  val loadedImage = IMG_Load (filename)
in
  if ref_is_null loadedImage then loadedImage else let
    val optimizedImage = SDL_DisplayFormat (loadedImage)
    val () = SDL_FreeSurface (loadedImage)
  in
    if ref_is_null (optimizedImage) then optimizedImage else let
      // Map the color key
      val (pf_format | p_format) = SDL_Surface_format (optimizedImage)
      val colorkey = SDL_MapRGB (!p_format, (Uint8)0, (Uint8)0xFF, (Uint8)0xFF)
      prval () = minus_addback (pf_format | optimizedImage)
      //Set all pixels of color R 0, G 0xFF, B 0xFF to be transparent
      val _err = SDL_SetColorKey (optimizedImage, SDL_SRCCOLORKEY, colorkey)
    in
      optimizedImage
    end // end of [if]
  end // end of [if]
end // end of [load_image]

(* ****** ****** *)

extern
fun apply_surface {l1,l2:anz} (
    x: int, y: int, src: !SDL_Surface_ref l1, dst: !SDL_Surface_ref l2
  ) : void

implement apply_surface
  (x, y, src, dst) = () where {
  var offset: SDL_Rect // unintialized
  val () = offset.x := (Sint16)x and () = offset.y := (Sint16)y
  val _err = SDL_UpperBlit_ptr (src, null, dst, &offset)
} // end of [apply_surface]

(* ****** ****** *)

implement main () = () where {
//
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val screen = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
  ) // end of [val]
  val () = assert_errmsg (ref_is_notnull screen, #LOCATION)
  // Set the window caption
  val () = SDL_WM_SetCaption (
    stropt_some "Foo says \"Hello!\"", stropt_none
  ) // end of [val]
//
  val background = load_image ("background.png")
  val () = assert_errmsg (ref_is_notnull background, #LOCATION)
  val foo = load_image ("LazyFoo-lesson05/foo.png")
  val () = assert_errmsg (ref_is_notnull foo, #LOCATION)
//
  //Apply the surfaces to the screen
  val () = apply_surface (0, 0, background, screen)
  val () = apply_surface (240, 190, foo, screen)
//
  val _err = SDL_Flip (screen)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  var quit: bool = false
  var event: SDL_Event?
  val () = while (quit = false) let
    val () = while (true) begin
      if SDL_PollEvent (event) > 0 then let
        prval () = opt_unsome (event)
      in
        if SDL_Event_type event = SDL_QUIT then quit := true
      end else let
        prval () = opt_unnone (event)
      in
        break // loop exit
      end // end of [if]
    end // end of [val]
  in
    // nothing
  end // end of [val]
//
  val () = SDL_FreeSurface (background)
  val () = SDL_FreeSurface (foo)
  val _ptr = SDL_Quit_screen (screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson05.dats] *)