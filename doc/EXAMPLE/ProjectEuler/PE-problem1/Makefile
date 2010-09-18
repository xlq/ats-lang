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
  problem1-hwxi \

######

problem1-hwxi: problem1-hwxi.dats
	$(ATSCC) -D_ATS_PROOFCHECK -o $@ problem1-hwxi.dats && ./problem1-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem1-hwxi

###### end of [Makefile] ######
