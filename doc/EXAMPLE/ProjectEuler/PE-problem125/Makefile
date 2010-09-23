######
#
# A simple Makefile
#
######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(or $(ATSHOMEQ), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem125-hwxi \

######

problem125-hwxi: problem125-hwxi.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o $@ problem125-hwxi.dats -lm && ./problem125-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem125-hwxi

###### end of [Makefile] ######
