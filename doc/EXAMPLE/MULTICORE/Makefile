##
## A simple Makefile
##

######

fib_mt: fib_mt.dats
	atscc -o fib_mt -O3 -D_ATS_MULTITHREAD fib_mt.dats -lpthread -lats_mt

partial-sums_mt: partial-sums_mt.dats
	atscc -o partial-sums_mt -O3 -D_ATS_MULTITHREAD partial-sums_mt.dats -lm -lpthread -lats_mt

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall: clean
	rm -f a.out
	rm -f fib_mt
	rm -f partial-sums_mt

###### end of [Makefile] ######
