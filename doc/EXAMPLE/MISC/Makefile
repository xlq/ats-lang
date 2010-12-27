######
#
# A variety of examples involving dependent and/or linear types
#
######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean
cleanall:: ; $(RMF) ./XREF/*
cleanall:: ; $(RMF) *_?ats.html

######

html::

######

#
# automatic differentiation
#
checkall:: AutoDiff
AutoDiff: AutoDiff.dats
#	$(ATSCC) -o AutoDiff -D_ATS_gc -O3 AutoDiff.dats -lm
#	$(ATSCC) -o AutoDiff -D_ATS_gcats -O3 AutoDiff.dats -lm
	$(ATSCC) -o AutoDiff -D_ATS_GCATS -O3 AutoDiff.dats -lm
cleanall:: ; $(RMF) AutoDiff

#
# BlackScholes formula
#
checkall:: BlackScholes
BlackScholes: BlackScholes.dats; $(ATSCC) -tc BlackScholes.dats
cleanall:: ; $(RMF) BlackScholes

#
# random number generation
#
checkall:: coin_flip
coin_flip: coin_flip.dats
	$(ATSCC) -O3 -o coin_flip coin_flip.dats && ./coin_flip
cleanall:: ; $(RMF) coin_flip

#
# an interesting curve
#
checkall:: curve
curve: curve.dats; $(ATSCC) -o curve curve.dats -lm # && ./curve
cleanall:: ; $(RMF) curve

#
# test for Mersenne primes
#
checkall:: fft
fft: fft.dats; $(ATSCC) -O3 -o fft fft.dats -lm
cleanall:: ; $(RMF) fft

#
# Garsia-Wachs
#
checkall:: GarsiaWachs
GarsiaWachs: GarsiaWachs.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o GarsiaWachs GarsiaWachs.dats \
     && ./GarsiaWachs
cleanall:: ; $(RMF) GarsiaWachs

#
# gaussian elimination
#
checkall:: GaussElim
GaussElim: GaussElim.dats
	$(ATSCC) -o GaussElim GaussElim.dats && ./GaussElim
cleanall:: ; $(RMF) GaussElim

#
# a multithreaded implementation of GCD
#
checkall:: gcd_mt
gcd_mt: gcd_mt.dats
	$(ATSCC) -o gcd_mt -O3 -D_ATS_MULTITHREAD gcd_mt.dats -lpthread -lats_mt \
     && ./gcd_mt 12345 67890
cleanall:: ; $(RMF) gcd_mt

#
# hamming in lazy style
#
checkall:: hamming_lazy
hamming_lazy: hamming_lazy.dats
	$(ATSCC) -o hamming_lazy hamming_lazy.dats && ./hamming_lazy
cleanall:: ; $(RMF) hamming_lazy

#
# hanoi tower
#
checkall:: hanoi
hanoi: hanoi.dats; $(ATSCC) -o hanoi hanoi.dats && ./hanoi
cleanall:: ; $(RMF) hanoi

#
# integer square root
#
checkall:: isqrt
isqrt: isqrt.dats; $(ATSCC) -o isqrt isqrt.dats && ./isqrt
cleanall:: ; $(RMF) isqrt

#
# Knuth-Morris-Pratt string search
#
checkall:: kmp
kmp: kmp.dats; $(ATSCC) -o kmp kmp.dats && ./kmp
cleanall:: ; $(RMF) kmp

#
# Monte Carlo method
#
checkall:: montecarlo
montecarlo: montecarlo.dats
	$(ATSCC) -O2 -o montecarlo montecarlo.dats -lm -lats_smlbas \
     && ./montecarlo
cleanall:: ; $(RMF) montecarlo

#
# An example of linear lazy evaluation
#
checkall:: longestline
longestline: longestline.dats
	$(ATSCC) -o longestline longestline.dats \
     && ./longestline < ./longestline.dats
cleanall:: ; $(RMF) longestline

#
# generating a password randomly
#
checkall:: passwdgen
passwdgen: passwdgen.dats
	$(ATSCC) -O3 -o passwdgen passwdgen.dats && ./passwdgen
cleanall:: ; $(RMF) passwdgen

#
# implementing natural numbers in ATS
#
checkall:: Peano
Peano: Peano.dats; $(ATSCC) -o Peano Peano.dats && ./Peano
cleanall:: ; $(RMF) Peano

#
# Euler's transform in lazy style
#
checkall:: pi_lazy
pi_lazy: pi_lazy.dats; $(ATSCC) -o pi_lazy pi_lazy.dats && ./pi_lazy
cleanall:: ; $(RMF) pi_lazy

#
# Verified quicksort implementations
#
checkall:: quicksort_list
quicksort_list: quicksort_list.dats
	$(ATSCC) -o $@ $< && ./quicksort_list
cleanall:: ; $(RMF) quicksort_list

checkall:: quicksort1_list
quicksort1_list: quicksort1_list.dats
	$(ATSCC) -D_ATS_PROOFCHECK -o $@ $< && ./quicksort1_list
cleanall:: ; $(RMF) quicksort1_list

checkall:: quicksort2_list
quicksort2_list: quicksort2_list.dats; $(ATSCC) -o $@ $< && ./quicksort2_list
cleanall:: ; $(RMF) quicksort2_list

#
# the n-queen problem
#
checkall:: queens
queens: queens.dats
	$(ATSCC) -o queens queens.dats && ./queens 4 > /dev/null
cleanall:: ; $(RMF) queens

checkall:: queens_appel
queens_appel: queens_appel.dats
	$(ATSCC) -o queens_appel queens_appel.dats && ./queens_appel
cleanall:: ; $(RMF) queens_appel

checkall:: queens_lazy_vt
queens_lazy_vt: queens_lazy_vt.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o queens_lazy_vt queens_lazy_vt.dats && ./queens_lazy_vt
cleanall:: ; $(RMF) queens_lazy_vt

#
# Erathosthene's sieve
#
checkall:: sieve
sieve: sieve.dats; $(ATSCC) -o sieve sieve.dats # && ./sieve
cleanall:: ; $(RMF) sieve

checkall:: sieve_lazy
sieve_lazy: sieve_lazy.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o sieve_lazy sieve_lazy.dats # && ./sieve_lazy
cleanall:: ; $(RMF) sieve_lazy

checkall:: sieve_lazy_vt
sieve_lazy_vt: sieve_lazy_vt.dats
#	$(ATSCC) -O3 -o sieve_lazy_vt sieve_lazy_vt.dats
#	$(ATSCC) -D_ATS_gcats -O3 -o sieve_lazy_vt sieve_lazy_vt.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o sieve_lazy_vt sieve_lazy_vt.dats # && ./sieve_lazy_vt
cleanall:: ; $(RMF) sieve_lazy_vt

#
# a simple implementation of string match in CPS-style
#
checkall:: strmat
strmat: strmat.dats; $(ATSCC) -o strmat strmat.dats
cleanall:: ; $(RMF) strmat

#
# programming in System F
#
checkall:: systemf_programming_examples
systemf_programming_examples: systemf_programming_examples.dats
	$(ATSCC) -O3 -o $@ $< && ./systemf_programming_examples
cleanall:: ; $(RMF) systemf_programming_examples

#
# a simple example of programming with theorem-proving
#
checkall:: sumup
sumup: sumup.dats
	$(ATSCC) -D_ATS_PROOFCHECK -O3 -o sumup sumup.dats && ./sumup
cleanall:: ; $(RMF) sumup

#
# a poor man's game of tetrix
#
checkall:: tetrix
tetrix: tetrix.dats; $(ATSCC) -O3 -o tetrix tetrix.dats
cleanall:: ; $(RMF) tetrix

#
# a simple implementation of world count
#
checkall:: wc
wc: wc.dats; $(ATSCC) -O3 -o wc wc.dats && ./wc *.dats
cleanall:: ; $(RMF) wc

######

html:: html_AutoDiff
html_AutoDiff: ; $(ATSOPT) --posmark_html -d AutoDiff.dats > AutoDiff_dats.html
html:: html_coin_flip
html_coin_flip: ; $(ATSOPT) --posmark_html -d coin_flip.dats > coin_flip_dats.html
html:: html_curve
html_curve: ; $(ATSOPT) --posmark_html -d curve.dats > curve_dats.html
html:: html_fft
html_fft: ; $(ATSOPT) --posmark_html -d fft.dats > fft_dats.html
html:: html_GaussElim
html_GaussElim: ; $(ATSOPT) --posmark_html -d GaussElim.dats > GaussElim_dats.html
html:: html_GarsiaWachs
html_GarsiaWachs: ; $(ATSOPT) --posmark_html -d GarsiaWachs.dats > GarsiaWachs_dats.html
html:: html_gcd_mt
html_gcd_mt: ; $(ATSOPT) --posmark_html -d gcd_mt.dats > gcd_mt_dats.html
html:: html_hanoi
html_hanoi: ; $(ATSOPT) --posmark_html -d hanoi.dats > hanoi_dats.html
html:: html_isqrt
html_isqrt: ; $(ATSOPT) --posmark_html -d isqrt.dats > isqrt_dats.html
html:: html_kmp
html_kmp: ; $(ATSOPT) --posmark_html -d kmp.dats > kmp_dats.html
html:: html_longestline
html_longestline: ; $(ATSOPT) --posmark_html -d longestline.dats > longestline_dats.html
html:: html_passwdgen
html_passwdgen: ; $(ATSOPT) --posmark_html -d passwdgen.dats > passwdgen_dats.html
html:: html_pi_lazy
html_pi_lazy: ; $(ATSOPT) --posmark_html -d pi_lazy.dats > pi_lazy_dats.html
html:: html_quicksort_list
html_quicksort_list:
	$(ATSOPT) --posmark_html -d quicksort_list.dats > quicksort_list_dats.html
html:: html_quicksort2_list
html_quicksort2_list:
	$(ATSOPT) --posmark_html -d quicksort2_list.dats > quicksort2_list_dats.html
html:: html_queens
html_queens: ; $(ATSOPT) --posmark_html -d queens.dats > queens_dats.html
html:: html_queens_appel
html_queens_appel: ; $(ATSOPT) --posmark_html -d queens_appel.dats > queens_appel_dats.html
html:: html_queens_lazy_vt
html_queens_lazy_vt: ; $(ATSOPT) --posmark_html -d queens_lazy_vt.dats > queens_lazy_vt_dats.html
html:: html_sieve
html_sieve: ; $(ATSOPT) --posmark_html -d sieve.dats > sieve_dats.html
html:: html_sieve_lazy
html_sieve_lazy: ; $(ATSOPT) --posmark_html -d sieve_lazy.dats > sieve_lazy_dats.html
html:: html_strmat
html_strmat: ; $(ATSOPT) --posmark_html -d strmat.dats > strmat_dats.html
html:: html_sumup
html_sumup: ; $(ATSOPT) --posmark_html -d sumup.dats > sumup_dats.html
html:: html_systemf_programming_examples
html_systemf_programming_examples:
	$(ATSOPT) --posmark_html -d systemf_programming_examples.dats > systemf_programming_examples_dats.html
html:: html_tetrix
html_tetrix: ; $(ATSOPT) --posmark_html -d tetrix.dats > tetrix_dats.html
html:: html_wc
html_wc: ; $(ATSOPT) --posmark_html -d wc.dats > wc_dats.html

######

xref::
	$(ATSOPT) --posmark_xref=XREF -d \
          $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
	$(ATSOPT) --posmark_xref=XREF -d AutoDiff.dats > AutoDiff_dats.html
	$(ATSOPT) --posmark_xref=XREF -d coin_flip.dats > coin_flip_dats.html
	$(ATSOPT) --posmark_xref=XREF -d curve.dats > curve_dats.html
	$(ATSOPT) --posmark_xref=XREF -d fft.dats > fft_dats.html
	$(ATSOPT) --posmark_xref=XREF -d GaussElim.dats > GaussElim_dats.html
	$(ATSOPT) --posmark_xref=XREF -d GarsiaWachs.dats > GarsiaWachs_dats.html
	$(ATSOPT) --posmark_xref=XREF -d gcd_mt.dats > gcd_mt_dats.html
	$(ATSOPT) --posmark_xref=XREF -d hanoi.dats > hanoi_dats.html
	$(ATSOPT) --posmark_xref=XREF -d isqrt.dats > isqrt_dats.html
	$(ATSOPT) --posmark_xref=XREF -d kmp.dats > kmp_dats.html
	$(ATSOPT) --posmark_xref=XREF -d longestline.dats > longestline_dats.html
	$(ATSOPT) --posmark_xref=XREF -d passwdgen.dats > passwdgen_dats.html
	$(ATSOPT) --posmark_xref=XREF -d pi_lazy.dats > pi_lazy_dats.html
	$(ATSOPT) --posmark_xref=XREF -d quicksort_list.dats > quicksort_list_dats.html
	$(ATSOPT) --posmark_xref=XREF -d quicksort2_list.dats > quicksort2_list_dats.html
	$(ATSOPT) --posmark_xref=XREF -d queens.dats > queens_dats.html
	$(ATSOPT) --posmark_xref=XREF -d queens_appel.dats > queens_appel_dats.html
	$(ATSOPT) --posmark_xref=XREF -d queens_lazy_vt.dats > queens_lazy_vt_dats.html
	$(ATSOPT) --posmark_xref=XREF -d sieve.dats > sieve_dats.html
	$(ATSOPT) --posmark_xref=XREF -d sieve_lazy.dats > sieve_lazy_dats.html
	$(ATSOPT) --posmark_xref=XREF -d sieve_lazy_vt.dats > sieve_lazy_vt_dats.html
	$(ATSOPT) --posmark_xref=XREF -d strmat.dats > strmat_dats.html
	$(ATSOPT) --posmark_xref=XREF -d sumup.dats > sumup_dats.html
	$(ATSOPT) --posmark_xref=XREF -d \
          systemf_programming_examples.dats > systemf_programming_examples_dats.html
	$(ATSOPT) --posmark_xref=XREF -d tetrix.dats > tetrix_dats.html
	$(ATSOPT) --posmark_xref=XREF -d wc.dats > wc_dats.html

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) ./MISC/*
	$(RMF) *_dats.c *_sats.c

###### end of [Makefile] ######
