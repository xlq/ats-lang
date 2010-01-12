#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: January, 2010
#

ATSCC="$(ATSHOME)"/bin/atscc

######

all: atsctrb_SDL.o clean

######

atsctrb_SDL.o: \
  SDL_sats.o SDL_dats.o SDL_image_sats.o SDL_ttf_sats.o
	ld -r -o $@ \
  SDL_sats.o SDL_dats.o SDL_image_sats.o SDL_ttf_sats.o

######

SDL_sats.o: \
   SATS/SDL.sats \
   SATS/SDL_timer.sats \
   SATS/SDL_video.sats \

	$(ATSCC) -o $@ -c SATS/SDL.sats

SDL_dats.o: DATS/SDL.dats
	$(ATSCC) -o $@ -c DATS/SDL.dats

######

SDL_image_sats.o: \
   SATS/SDL_image.sats \

	$(ATSCC) -o $@ -c SATS/SDL_image.sats

SDL_ttf_sats.o: \
   SATS/SDL_ttf.sats \

	$(ATSCC) -o $@ -c SATS/SDL_ttf.sats

######

clean::
	rm -f SDL_sats.c SDL_sats.o
	rm -f SDL_dats.c SDL_dats.o
	rm -f SDL_ttf_sats.c SDL_ttf_sats.o

cleanall: clean
	rm -f atsctrb_SDL.o

###### end of [Makefile] ######
