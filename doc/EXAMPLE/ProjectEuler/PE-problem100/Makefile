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
  problem100-hwxi \

######

problem100-hwxi: problem100-hwxi.dats
	$(ATSCC) -O2 -o $@ problem100-hwxi.dats -lm && ./problem100-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem100-hwxi

###### end of [Makefile] ######
