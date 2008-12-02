GCC=gcc
ATSCC="$(ATSHOME)"/bin/atscc

all: binary-trees binary-trees-ref \
     fannkuch fannkuch_smp fasta k-nucleotide \
     mandelbrot n-body nsieve nsieve-bits partial-sums \
     pidigits recursive reverse-complement spectral-norm \
     sum-file thread-ring \

binary-trees: binary-trees.dats
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_gc
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_gcats
	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_GCATS

binary-trees-ref: binary-trees-ref.dats
#	$(ATSCC) -O3 binary-trees-ref.dats -o binary-trees-ref
#	$(ATSCC) -O3 binary-trees-ref.dats -o binary-trees-ref -D_ATS_gc
#	$(ATSCC) -O3 binary-trees-ref.dats -o binary-trees-ref -D_ATS_gcats
	$(ATSCC) -O3 binary-trees-ref.dats -o binary-trees-ref -D_ATS_GCATS

fannkuch_c: fannkuch.c
	$(GCC) -O3 -fomit-frame-pointer fannkuch.c -o fannkuch_c
fannkuch: fannkuch.dats
	$(ATSCC) -O3 -fomit-frame-pointer fannkuch.dats -o fannkuch
fannkuch_smp: fannkuch_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer fannkuch_smp.dats -o fannkuch_smp -lpthread

fasta: fasta.dats; $(ATSCC) -msse2 -O3 fasta.dats -o fasta

k-nucleotide: k-nucleotide.dats symtbl.dats
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_gc
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_gcats
	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_GCATS

k-nucleotide_cpp: k-nucleotide.cpp
	/usr/bin/g++ -O3 -fomit-frame-pointer k-nucleotide.cpp -o k-nucleotide_cpp

mandelbrot: mandelbrot.dats
	$(ATSCC) -O3 mandelbrot.dats -o mandelbrot
mandelbrot_simd: mandelbrot_simd.dats
	$(ATSCC) -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot_simd mandelbrot_simd.dats
mandelbrot_simd_smp: mandelbrot_simd_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot_simd_smp mandelbrot_simd_smp.dats -lpthread
mandelbrot_simd_smp1: mandelbrot_simd_smp1.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot_simd_smp1 mandelbrot_simd_smp1.dats -lpthread
mandelbrot_c: mandelbrot.c
	$(GCC) -Wall -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -lm mandelbrot.c -o mandelbrot_c


n-body: n-body.dats
	$(ATSCC) -O3 n-body.dats -o n-body -lm

nsieve: nsieve.dats
	$(ATSCC) -O3 nsieve.dats -o nsieve

nsieve-mt: nsieve-mt.dats
	$(ATSCC) -O3 nsieve-mt.dats -o nsieve-mt -lm

nsieve-bits: nsieve-bits.dats
	$(ATSCC) -O3 nsieve-bits.dats -o nsieve-bits

partial-sums: partial-sums.dats
	$(ATSCC) -O3 partial-sums.dats -o partial-sums -lm

pidigits: pidigits.dats
	$(ATSCC) -O3 pidigits.dats -o pidigits -lgmp

recursive: recursive.dats
	$(ATSCC) -O3 -fomit-frame-pointer recursive.dats -o recursive

regex-dna: regex-dna.dats
#	$(ATSCC) -O3 regex-dna.dats -o regex-dna -lpcre
#	$(ATSCC) -D_ATS_GCATS -O3 -fomit-frame-pointer regex-dna.dats -o regex-dna -lpcre
	$(ATSCC) -D_ATS_GCATS -O3 regex-dna.dats -o regex-dna -lpcre

reverse-complement: reverse-complement.dats
	$(ATSCC) -O3 reverse-complement.dats -o reverse-complement

spectral-norm: spectral-norm.dats
	$(ATSCC) -O3 spectral-norm.dats -o spectral-norm -lm

sum-file: sum-file.dats
	$(ATSCC) -O3 sum-file.dats -o sum-file

thread-ring: thread-ring.dats
	$(ATSCC) -O3 thread-ring.dats -o thread-ring -lpthread

######
#
# update
#
######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/SHOOTOUT

update::
	cp Makefile $(DIR)
	cp binary-trees.dats $(DIR)
	cp binary-trees-ref.dats $(DIR)
	cp fannkuch.dats $(DIR)
	cp fannkuch_smp.dats $(DIR)
	cp fasta.dats $(DIR)
	cp k-nucleotide.dats $(DIR)
	cp mandelbrot.dats $(DIR)
	cp n-body.dats $(DIR)
	cp nsieve.dats $(DIR)
	cp nsieve-bits.dats $(DIR)
	cp partial-sums.dats $(DIR)
	cp pidigits.dats $(DIR)
	cp recursive.dats $(DIR)
	cp reverse-complement.dats $(DIR)
	cp spectral-norm.dats $(DIR)
	cp sum-file.dats $(DIR)
	cp symtbl.dats $(DIR)

######
#
# cleanup
#
######

clean::
	rm -f a.out *_dats.c *_sats.c *~

cleanall: clean
	rm -f binary-trees
	rm -f binary-trees-ref
	rm -f fannkuch
	rm -f fannkuch_smp
	rm -f fasta
	rm -f k-nucleotide
	rm -f mandelbrot
	rm -f mandelbrot_simd
	rm -f mandelbrot_simd_smp
	rm -f mandelbrot_simd_smp1
	rm -f n-body
	rm -f nsieve
	rm -f nsieve-bits
	rm -f partial-sums
	rm -f pidigits
	rm -f recursive
	rm -f regex-dna
	rm -f reverse-complement
	rm -f spectral-norm
	rm -f sum-file
	rm -f thread-ring
