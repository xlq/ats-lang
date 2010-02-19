#
#
# Makefile for SHOOTOUT submissions
#
#

ATSCC="$(ATSHOME)"/bin/atscc
ATSOPT="$(ATSHOME)"/bin/atsopt
CC=$(HOME)/gcc-4.3.2/bin/gcc

all: \
  binary-trees binary-trees2 \
  fannkuch fannkuch2 \
  fasta fasta2 fasta4 \
  k-nucleotide k-nucleotide2 \
  mandelbrot \
  n-body n-body2 \
  pidigits pidigits2 pidigits3 \
  regex-dna regex-dna2 \
  reverse-complement reverse-complement2 \
  spectral-norm spectral-norm2 \
  thread-ring \

binary-trees: binary-trees.dats
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_gc
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_gcats
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_GCATS
	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_GCBDW

binary-trees_smp: binary-trees_smp_dats.c
#	$(ATSCC) -D_ATS_MULTITHREAD -D_ATS_GCBDW -O3 -g binary-trees_smp_dats.c -o binary-trees_smp -lpthread
	$(ATSCC) -D_ATS_MULTITHREAD -D_ATS_GCATS -O3 -g binary-trees_smp_dats.c -o binary-trees_smp -lpthread
#	$(ATSCC) -D_ATS_MULTITHREAD -D_ATS_gc -O3 -g binary-trees_smp_dats.c -o binary-trees_smp -lpthread

binary-trees_smp_dats.c: binary-trees_smp.dats
	$(ATSOPT) -o binary-trees_smp_dats.c -d binary-trees_smp.dats

binary-trees2: binary-trees2.dats
	$(ATSCC) -O3 binary-trees2.dats -o binary-trees2 -D_ATS_GCATS

binary-trees2_smp: binary-trees2_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 binary-trees2_smp.dats -o binary-trees2_smp -D_ATS_GCATS -lpthread

######

fannkuch: fannkuch.dats
	$(ATSCC) -fomit-frame-pointer -O3 fannkuch.dats -o fannkuch
fannkuch1: fannkuch1.dats
	$(ATSCC) -fomit-frame-pointer -O3 fannkuch1.dats -o fannkuch1
fannkuch2: fannkuch2.dats
	$(ATSCC) -fomit-frame-pointer -O3 fannkuch2.dats -o fannkuch2

fannkuch_smp: fannkuch_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer fannkuch_smp.dats -o fannkuch_smp -lpthread
fannkuch_smp1: fannkuch_smp1.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer fannkuch_smp1.dats -o fannkuch_smp1 -lpthread


fasta: fasta.dats
	$(ATSCC) -msse2 -mfpmath=sse -O3 fasta.dats -o fasta

fasta2: fasta2.dats
	$(ATSCC) -msse2 -mfpmath=sse -O3 fasta2.dats -o fasta2

fasta4: fasta4.dats
	$(ATSCC) -msse2 -mfpmath=sse -O3 fasta4.dats -o fasta4

k-nucleotide: k-nucleotide.dats
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_gc
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_gcats
	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_GCATS
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide

k-nucleotide1: k-nucleotide1.dats
	$(ATSCC) -D_ATS_GCATS -O3 k-nucleotide1.dats hashtable.dats -o k-nucleotide1

k-nucleotide2: k-nucleotide2.dats
	$(ATSCC) -D_ATS_GCATS -O3 k-nucleotide2.dats -o k-nucleotide2
#	$(ATSCC) -O3 k-nucleotide2.dats -o k-nucleotide2

k-nucleotide3: k-nucleotide3.dats
	$(ATSCC) -D_ATS_GCATS -O3 k-nucleotide3.dats funmset_avltree.dats -o k-nucleotide3
#	$(ATSCC) -O3 k-nucleotide3.dats -o k-nucleotide3

mandelbrot: mandelbrot.dats
	$(ATSCC) -msse2 -O3 mandelbrot.dats -o mandelbrot
mandelbrot_simd: mandelbrot_simd.dats
	$(ATSCC) -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot_simd mandelbrot_simd.dats
mandelbrot_simd_smp: mandelbrot_simd_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot_simd_smp mandelbrot_simd_smp.dats -lpthread

######

n-body: n-body.dats
	$(ATSCC) -msse2 -mfpmath=sse -O3 n-body.dats -o n-body -lm
n-body1: n-body1.dats
	$(ATSCC) -msse2 -mfpmath=sse -O3 n-body1.dats -o n-body1 -lm
n-body_smp: n-body_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -msse2 -mfpmath=sse -O3 n-body_smp.dats -o n-body_smp -lm -lpthread

n-body2: n-body2.dats
	$(ATSCC) -fomit-frame-pointer -msse2 -mfpmath=sse -O3 n-body2.dats -o n-body2 -lm

n-body2_c: n-body2.c
	$(ATSCC) -fomit-frame-pointer -msse2 -mfpmath=sse -O3 n-body2.c -o n-body2_c -lm

######

pidigits: pidigits.dats
	$(ATSCC) -O3 -fomit-frame-pointer pidigits.dats -o pidigits -lgmp

pidigits2: pidigits2.dats
	$(ATSCC) -O3 -fomit-frame-pointer pidigits2.dats -o pidigits2 -lgmp

pidigits3: pidigits3.dats
	$(ATSCC) -O3 -fomit-frame-pointer pidigits3.dats -o pidigits3 -lgmp

regex-dna: regex-dna.dats
	$(ATSCC) -D_ATS_GCATS -O3 -fomit-frame-pointer regex-dna.dats -o regex-dna -lpcre

regex-dna_smp: regex-dna_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer regex-dna_smp.dats -o regex-dna_smp -lpthread -lpcre

regex-dna2: regex-dna2.dats
	$(ATSCC) -D_ATS_GCATS -O3 -fomit-frame-pointer regex-dna2.dats -o regex-dna2 -lpcre

######

reverse-complement: reverse-complement.dats
	$(ATSCC) -O3 -fomit-frame-pointer reverse-complement.dats -o reverse-complement

reverse-complement2: reverse-complement2.dats
	$(ATSCC) -O3 -fomit-frame-pointer reverse-complement2.dats -o reverse-complement2

######

spectral-norm: spectral-norm.dats
	$(ATSCC) -O3 -fomit-frame-pointer -msse2 spectral-norm.dats -o spectral-norm -lm
spectral-norm_smp: spectral-norm_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer -msse2 spectral-norm_smp.dats -o spectral-norm_smp -lm -lpthread

spectral-norm1: spectral-norm1.dats
	$(ATSCC) -O3 -fomit-frame-pointer -msse2 spectral-norm1.dats -o spectral-norm1 -lm

spectral-norm1_simd: spectral-norm1_simd.dats
	$(ATSCC) -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o spectral-norm1_simd spectral-norm1_simd.dats -lm

spectral-norm2: spectral-norm2.dats
	$(ATSCC) -O3 -fomit-frame-pointer -msse3 spectral-norm2.dats -o spectral-norm2 -lm

######

thread-ring: thread-ring.dats
	$(ATSCC) -O3 -fomit-frame-pointer thread-ring.dats -o thread-ring -lpthread

###### update ######


###### cleanup ######

clean:: ; rm -f a.out *_dats.c *_sats.c *~

cleanall: clean
	rm -f binary-trees
	rm -f binary-trees_smp
	rm -f binary-trees2
	rm -f fannkuch
	rm -f fannkuch_smp
	rm -f fannkuch_smp1
	rm -f fannkuch1
	rm -f fannkuch2
	rm -f fasta
	rm -f fasta_smp
	rm -f fasta2
	rm -f fasta4
	rm -f fasta_output.txt
	rm -f k-nucleotide
	rm -f k-nucleotide2
	rm -f mandelbrot
	rm -f mandelbrot_simd
	rm -f mandelbrot_simd_smp
	rm -f n-body
	rm -f n-body_smp
	rm -f n-body1
	rm -f n-body2
	rm -f pidigits
	rm -f pidigits2
	rm -f pidigits3
	rm -f regex-dna
	rm -f regex-dna_smp
	rm -f regex-dna2
	rm -f reverse-complement
	rm -f reverse-complement2
	rm -f spectral-norm
	rm -f spectral-norm_smp
	rm -f spectral-norm_smp2
	rm -f spectral-norm1
	rm -f spectral-norm1_simd
	rm -f spectral-norm2
	rm -f thread-ring

###### end of [Makefile] ######
