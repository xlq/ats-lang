all: fib_mt gcd_mt \
     mergesort_mt_int mergesort_mt_float \
     partial-sums_mt nsieve_mt

fib_mt: fib_mt.dats
#	atscc -o fib_mt -O3 -D_ATS_gc -D_ATS_MULTITHREAD -pthread fib_mt.dats
	atscc -o fib_mt -O3 -D_ATS_MULTITHREAD -pthread fib_mt.dats

gcd_mt: gcd_mt.dats
#	atscc -o gcd_mt -O3 -D_ATS_MULTITHREAD -pthread gcd_mt.dats
#	atscc -o gcd_mt -O3 -D_ATS_MULTITHREAD -D_ATS_gc -pthread gcd_mt.dats
	atscc -o gcd_mt -O3 -D_ATS_MULTITHREAD -D_ATS_GCATS -pthread gcd_mt.dats

partial-sums_mt: partial-sums_mt.dats
#	atscc -o partial-sums_mt -O3 -D_ATS_gc -D_ATS_MULTITHREAD -pthread partial-sums_mt.dats -lm
	atscc -o partial-sums_mt -O3 -D_ATS_MULTITHREAD -pthread partial-sums_mt.dats -lm

mergesort_mt_int: mergesort_mt_int.dats mergesort_mt.dats
#	atscc -o mergesort_mt_int -O3 -D_ATS_gc -D_ATS_MULTITHREAD -pthread mergesort_mt_int.dats -lm
	atscc -o mergesort_mt_int -O3 -D_ATS_MULTITHREAD -pthread mergesort_mt_int.dats -lm

mergesort_mt_float: mergesort_mt_float.dats mergesort_mt.dats
#	atscc -o mergesort_mt_float -O3 -D_ATS_gc -D_ATS_MULTITHREAD -pthread mergesort_mt_float.dats -lm
	atscc -o mergesort_mt_float -O3 -D_ATS_MULTITHREAD -pthread mergesort_mt_float.dats -lm

quicksort_mt_int: quicksort_mt_int.dats quicksort_mt.dats
#	atscc -o quicksort_mt_int -O3 -D_ATS_gc -D_ATS_MULTITHREAD -pthread quicksort_mt_int.dats -lm
	atscc -o quicksort_mt_int -O3 -D_ATS_MULTITHREAD -pthread quicksort_mt_int.dats -lm

quicksort_mt_float: quicksort_mt_float.dats quicksort_mt.dats
#	atscc -o quicksort_mt_float -O3 -D_ATS_gc -D_ATS_MULTITHREAD -pthread quicksort_mt_float.dats -lm
	atscc -o quicksort_mt_float -O3 -D_ATS_MULTITHREAD -pthread quicksort_mt_float.dats -lm

nsieve_mt: nsieve_mt.dats
#	atscc -o nsieve_mt -O3 -D_ATS_gc -D_ATS_MULTITHREAD -pthread nsieve_mt.dats -lm
	atscc -o nsieve_mt -O3 -D_ATS_MULTITHREAD -pthread nsieve_mt.dats -lm

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall: clean
	rm -f a.out
	rm -f fib
	rm -f fib_mt
	rm -f gcd_mt
	rm -f mergesort_mt_int
	rm -f mergesort_mt_float
	rm -f quicksort_mt_int
	rm -f quicksort_mt_float
	rm -f nsieve_mt
	rm -f partial-sums_mt

