######
#
# A variety of examples involving dependent and/or linear types
#
######

ATSCC="$(ATSHOME)/bin/atscc"

######

all: AutoDiff fft \
     hamming_lazy \
     GaussElim GarsiaWachs \
     kmp queens pi_lazy \
     sieve sieve_lazy \
     strmat sumup \
     tetrix wc

# automatic differentiation
AutoDiff: AutoDiff.dats
#	$(ATSCC) -o AutoDiff -D_ATS_gc -O3 AutoDiff.dats -lm
#	$(ATSCC) -o AutoDiff -D_ATS_gcats -O3 AutoDiff.dats -lm
	$(ATSCC) -o AutoDiff -D_ATS_GCATS -O3 AutoDiff.dats -lm

# BlackScholes formula
BlackScholes: BlackScholes.dats; $(ATSCC) -tc BlackScholes.dats

# test for Mersenne primes
fft: fft.dats; $(ATSCC) -O3 -o fft fft.dats -lm

# Garsia-Wachs
GarsiaWachs: GarsiaWachs.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o GarsiaWachs GarsiaWachs.dats


# gaussian elimination
GaussElim: GaussElim.dats; $(ATSCC) -o GaussElim GaussElim.dats

# hamming in lazy style
hamming_lazy: hamming_lazy.dats
	$(ATSCC) -o hamming_lazy hamming_lazy.dats

# hanoi tower
hanoi: hanoi.dats; $(ATSCC) -o hanoi hanoi.dats

# Knuth-Morris-Pratt string search
kmp: kmp.dats; $(ATSCC) -o kmp kmp.dats

# the n-queen problem
queens: queens.dats; $(ATSCC) -o queens queens.dats

# generating a password randomly
passwdgen: passwdgen.dats; $(ATSCC) -O3 -o passwdgen passwdgen.dats

# Euler's transform in lazy style
pi_lazy: pi_lazy.dats; $(ATSCC) -o pi_lazy pi_lazy.dats

# Erathosthene's sieve
sieve: sieve.dats; $(ATSCC) -o sieve sieve.dats

# Erathosthene's sieve in lazy style
sieve_lazy: sieve_lazy.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o sieve_lazy sieve_lazy.dats
sieve_lazy_vt: sieve_lazy_vt.dats
#	$(ATSCC) -O3 -o sieve_lazy_vt sieve_lazy_vt.dats
	$(ATSCC) -D_ATS_gcats -O3 -o sieve_lazy_vt sieve_lazy_vt.dats
#	$(ATSCC) -D_ATS_GCATS -O3 -o sieve_lazy_vt sieve_lazy_vt.dats

# a simple implementation of string match in CPS-style
strmat: strmat.dats; $(ATSCC) -o strmat strmat.dats

# a simple example of programming with theorem-proving
sumup: sumup.dats; $(ATSCC) -O3 -o sumup sumup.dats

# a poor man's game of tetrix
tetrix: tetrix.dats; $(ATSCC) -O3 -o tetrix tetrix.dats

# a simple implementation of world count
wc: wc.dats; $(ATSCC) -O3 -o wc wc.dats

######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/MISC

update::
	cp Makefile $(DIR)
	cp AutoDiff.dats $(DIR)
	cp fft.dats $(DIR)
	cp GaussElim.dats $(DIR)
	cp GarsiaWachs.dats $(DIR)
	cp hamming_lazy.dats $(DIR)
	cp hanoi.dats $(DIR)
	cp kmp.dats $(DIR)
	cp passwdgen.dats $(DIR)
	cp pi_lazy.dats $(DIR)
	cp queens.dats $(DIR)
	cp sieve.dats $(DIR)
	cp sieve_lazy.dats $(DIR)
	cp strmat.dats $(DIR)
	cp sumup.dats $(DIR)
	cp tetrix.dats $(DIR)
	cp wc.dats $(DIR)

######

clean:: ; rm -f *_dats.c *_sats.c *~

cleanall:: clean
	rm -f a.out
	rm -f AutoDiff
	rm -f fft
	rm -f GaussElim
	rm -f GarsiaWachs
	rm -f hamming_lazy
	rm -f hanoi
	rm -f kmp
	rm -f passwdgen
	rm -f pi_lazy
	rm -f queens
	rm -f sieve
	rm -f strmat
	rm -f sieve_lazy
	rm -f sieve_lazy_vt
	rm -f tetrix
	rm -f sumup
	rm -f wc

###### end of [Makefile] ######
