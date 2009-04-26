######
#
# TIGERATS: A Tiger compiler written in ATS
#
# Makefile for testing the TIGERATS compiler
#
# Author: Hongwei Xi
#
# Time: Spring, 2009
#
######

GCC=gcc
TIGDIR=..
TIGCOMP=$(TIGDIR)/comptig

######

all:: \
  ack evenodd \
  f91 fact1 fact2 \
  fib1 fib2 fib3 fib4 \
  intpair hanoi listops \
  merge prettyprint \
  queens0 queens1 \

######

chmod::
	chmod 644 Makefile *.tig *_tig.s

######

ack: ack.tig
	$(TIGCOMP) ack.tig > ack_tig.s
	$(GCC) -o ack ack_tig.s $(TIGDIR)/tiger_prelude.c

######

evenodd: evenodd.tig
	$(TIGCOMP) evenodd.tig > evenodd_tig.s
	$(GCC) -o evenodd evenodd_tig.s $(TIGDIR)/tiger_prelude.c

######

f91: f91.tig
	$(TIGCOMP) f91.tig > f91_tig.s
	$(GCC) -o f91 f91_tig.s $(TIGDIR)/tiger_prelude.c

######

fact1: fact1.tig
	$(TIGCOMP) fact1.tig > fact1_tig.s
	$(GCC) -o fact1 fact1_tig.s $(TIGDIR)/tiger_prelude.c

fact2: fact2.tig
	$(TIGCOMP) fact2.tig > fact2_tig.s
	$(GCC) -o fact2 fact2_tig.s $(TIGDIR)/tiger_prelude.c
######

fib1: fib1.tig
	$(TIGCOMP) fib1.tig > fib1_tig.s
	$(GCC) -o fib1 fib1_tig.s $(TIGDIR)/tiger_prelude.c

fib2: fib2.tig
	$(TIGCOMP) fib2.tig > fib2_tig.s
	$(GCC) -o fib2 fib2_tig.s $(TIGDIR)/tiger_prelude.c

fib3: fib3.tig
	$(TIGCOMP) fib3.tig > fib3_tig.s
	$(GCC) -o fib3 fib3_tig.s $(TIGDIR)/tiger_prelude.c

fib4: fib4.tig
	$(TIGCOMP) fib4.tig > fib4_tig.s
	$(GCC) -o fib4 fib4_tig.s $(TIGDIR)/tiger_prelude.c

######

hanoi: hanoi.tig
	$(TIGCOMP) hanoi.tig > hanoi_tig.s
	$(GCC) -o hanoi hanoi_tig.s $(TIGDIR)/tiger_prelude.c

######

intpair: intpair.tig
	$(TIGCOMP) intpair.tig > intpair_tig.s
	$(GCC) -o intpair intpair_tig.s $(TIGDIR)/tiger_prelude.c

######

listops: listops.tig
	$(TIGCOMP) listops.tig > listops_tig.s
	$(GCC) -o listops listops_tig.s $(TIGDIR)/tiger_prelude.c

######

merge: merge.tig
	$(TIGCOMP) merge.tig > merge_tig.s
	$(GCC) -o merge merge_tig.s $(TIGDIR)/tiger_prelude.c

######

prettyprint: prettyprint.tig
	$(TIGCOMP) prettyprint.tig > prettyprint_tig.s
	$(GCC) -o prettyprint prettyprint_tig.s $(TIGDIR)/tiger_prelude.c

######

queens0: queens0.tig
	$(TIGCOMP) queens0.tig > queens0_tig.s
	$(GCC) -o queens0 queens0_tig.s $(TIGDIR)/tiger_prelude.c

queens1: queens1.tig
	$(TIGCOMP) queens1.tig > queens1_tig.s
	$(GCC) -o queens1 queens1_tig.s $(TIGDIR)/tiger_prelude.c

######

sum: sum.tig
	$(TIGCOMP) sum.tig > sum_tig.s
	$(GCC) -o sum sum_tig.s $(TIGDIR)/tiger_prelude.c

######

clean::
	rm -f ack evenodd
	rm -f f91 fact1 fact2
	rm -f fib1 fib2 fib3 fib4
	rm -f intpair hanoi listops
	rm -f merge prettyprint
	rm -f queens0 queens1 sum

cleanall: clean
	rm -f *_tig.s

###### end of [Makefile] ######
