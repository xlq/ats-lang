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
  problem123-hwxi \

######

problem123-hwxi: problem123-hwxi.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o $@ problem123-hwxi.dats -lm && ./problem123-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem123-hwxi

###### end of [Makefile] ######
