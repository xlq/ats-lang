######
#
# A variety of examples involving dependent and/or linear types
#
######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all
all: checkall

######

checkall: compall cleanall

######

compall: AutoDiff coin_flip \
     curve fft hamming_lazy \
     GaussElim GarsiaWachs \
     gcd_mt hanoi isqrt kmp \
     longestline montecarlo \
     quicksort_list quicksort2_list \
     queens queens_appel queens_lazy_vt \
     longestline passwdgen pi_lazy \
     sieve sieve_lazy sieve_lazy_vt \
     strmat sumup \
     systemf_programming_examples \
     tetrix wc \

# automatic differentiation
AutoDiff: AutoDiff.dats
#	$(ATSCC) -o AutoDiff -D_ATS_gc -O3 AutoDiff.dats -lm
#	$(ATSCC) -o AutoDiff -D_ATS_gcats -O3 AutoDiff.dats -lm
	$(ATSCC) -o AutoDiff -D_ATS_GCATS -O3 AutoDiff.dats -lm

# BlackScholes formula
BlackScholes: BlackScholes.dats; $(ATSCC) -tc BlackScholes.dats

# random number generation
coin_flip: coin_flip.dats
	$(ATSCC) -O3 -o coin_flip coin_flip.dats && ./coin_flip

# an interesting curve
curve: curve.dats; $(ATSCC) -o curve curve.dats -lm # && ./curve

# test for Mersenne primes
fft: fft.dats; $(ATSCC) -O3 -o fft fft.dats -lm

# Garsia-Wachs
GarsiaWachs: GarsiaWachs.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o GarsiaWachs GarsiaWachs.dats \
     && ./GarsiaWachs

# gaussian elimination
GaussElim: GaussElim.dats
	$(ATSCC) -o GaussElim GaussElim.dats && ./GaussElim

# a multithreaded implementation of GCD
gcd_mt: gcd_mt.dats
	$(ATSCC) -o gcd_mt -O3 -D_ATS_MULTITHREAD gcd_mt.dats -lpthread -lats_mt \
     && ./gcd_mt 12345 67890

# hamming in lazy style
hamming_lazy: hamming_lazy.dats
	$(ATSCC) -o hamming_lazy hamming_lazy.dats && ./hamming_lazy

# hanoi tower
hanoi: hanoi.dats; $(ATSCC) -o hanoi hanoi.dats && ./hanoi

# integer square root
isqrt: isqrt.dats; $(ATSCC) -o isqrt isqrt.dats && ./isqrt

# Knuth-Morris-Pratt string search
kmp: kmp.dats; $(ATSCC) -o kmp kmp.dats && ./kmp

montecarlo: montecarlo.dats
	$(ATSCC) -O2 -o montecarlo montecarlo.dats -lm -lats_smlbas \
     && ./montecarlo

# An example of linear lazy evaluation
longestline: longestline.dats
	$(ATSCC) -o longestline longestline.dats \
     && ./longestline < ./longestline.dats

# generating a password randomly
passwdgen: passwdgen.dats
	$(ATSCC) -O3 -o passwdgen passwdgen.dats && ./passwdgen

Peano: Peano.dats; $(ATSCC) -o Peano Peano.dats

# Euler's transform in lazy style
pi_lazy: pi_lazy.dats; $(ATSCC) -o pi_lazy pi_lazy.dats && ./pi_lazy

# Verified quicksort implementations
quicksort_list: quicksort_list.dats
	$(ATSCC) -D_ATS_PROOFCHECK -o quicksort_list quicksort_list.dats
quicksort2_list: quicksort2_list.dats
	$(ATSCC) -o quicksort2_list quicksort2_list.dats

# the n-queen problem
queens: queens.dats
	$(ATSCC) -o queens queens.dats && ./queens 4 > /dev/null

queens_appel: queens_appel.dats
	$(ATSCC) -o queens_appel queens_appel.dats && ./queens_appel

queens_lazy_vt: queens_lazy_vt.dats
	$(ATSCC) -O3 -o queens_lazy_vt queens_lazy_vt.dats -D_ATS_GCATS

# Erathosthene's sieve
sieve: sieve.dats; $(ATSCC) -o sieve sieve.dats

# Erathosthene's sieve in lazy style
sieve_lazy: sieve_lazy.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o sieve_lazy sieve_lazy.dats
sieve_lazy_vt: sieve_lazy_vt.dats
#	$(ATSCC) -O3 -o sieve_lazy_vt sieve_lazy_vt.dats
#	$(ATSCC) -D_ATS_gcats -O3 -o sieve_lazy_vt sieve_lazy_vt.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o sieve_lazy_vt sieve_lazy_vt.dats

# a simple implementation of string match in CPS-style
strmat: strmat.dats; $(ATSCC) -o strmat strmat.dats

systemf_programming_examples: \
  systemf_programming_examples.dats
	$(ATSCC) -O3 -o $@ $< && ./systemf_programming_examples

# a simple example of programming with theorem-proving
sumup: sumup.dats; $(ATSCC) -D_ATS_PROOFCHECK -O3 -o sumup sumup.dats && ./sumup

# a poor man's game of tetrix
tetrix: tetrix.dats; $(ATSCC) -O3 -o tetrix tetrix.dats

# a simple implementation of world count
wc: wc.dats; $(ATSCC) -O3 -o wc wc.dats && ./wc *.dats

######

html::
	$(ATSOPT) --posmark_html -d AutoDiff.dats > AutoDiff_dats.html
	$(ATSOPT) --posmark_html -d coin_flip.dats > coin_flip_dats.html
	$(ATSOPT) --posmark_html -d curve.dats > curve_dats.html
	$(ATSOPT) --posmark_html -d fft.dats > fft_dats.html
	$(ATSOPT) --posmark_html -d GaussElim.dats > GaussElim_dats.html
	$(ATSOPT) --posmark_html -d GarsiaWachs.dats > GarsiaWachs_dats.html
	$(ATSOPT) --posmark_html -d gcd_mt.dats > gcd_mt_dats.html
	$(ATSOPT) --posmark_html -d hanoi.dats > hanoi_dats.html
	$(ATSOPT) --posmark_html -d isqrt.dats > isqrt_dats.html
	$(ATSOPT) --posmark_html -d kmp.dats > kmp_dats.html
	$(ATSOPT) --posmark_html -d longestline.dats > longestline_dats.html
	$(ATSOPT) --posmark_html -d passwdgen.dats > passwdgen_dats.html
	$(ATSOPT) --posmark_html -d pi_lazy.dats > pi_lazy_dats.html
	$(ATSOPT) --posmark_html -d quicksort_list.dats > quicksort_list_dats.html
	$(ATSOPT) --posmark_html -d quicksort2_list.dats > quicksort2_list_dats.html
	$(ATSOPT) --posmark_html -d queens.dats > queens_dats.html
	$(ATSOPT) --posmark_html -d queens_appel.dats > queens_appel_dats.html
	$(ATSOPT) --posmark_html -d queens_lazy_vt.dats > queens_lazy_vt_dats.html
	$(ATSOPT) --posmark_html -d sieve.dats > sieve_dats.html
	$(ATSOPT) --posmark_html -d sieve_lazy.dats > sieve_lazy_dats.html
	$(ATSOPT) --posmark_html -d strmat.dats > strmat_dats.html
	$(ATSOPT) --posmark_html -d sumup.dats > sumup_dats.html
	$(ATSOPT) --posmark_html -d tetrix.dats > tetrix_dats.html
	$(ATSOPT) --posmark_html -d wc.dats > wc_dats.html

######

clean::
	rm -f MISC/*
	rm -f *_dats.c *_sats.c *_dats.html *_sats.html *~

cleanall:: clean
	rm -f a.out
	rm -f AutoDiff
	rm -f coin_flip
	rm -f curve
	rm -f fft
	rm -f GaussElim
	rm -f GarsiaWachs
	rm -f gcd_mt
	rm -f hamming_lazy
	rm -f hanoi
	rm -f isqrt
	rm -f kmp
	rm -f longestline
	rm -f montecarlo
	rm -f passwdgen
	rm -f Peano
	rm -f pi_lazy
	rm -f quicksort_list
	rm -f quicksort2_list
	rm -f queens
	rm -f queens_appel
	rm -f queens_lazy_vt
	rm -f sieve
	rm -f strmat
	rm -f sieve_lazy
	rm -f sieve_lazy_vt
	rm -f sumup
	rm -f systemf_programming_examples
	rm -f tetrix
	rm -f wc

###### end of [Makefile] ######
