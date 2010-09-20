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
  problem51-hwxi \

######

problem51-hwxi: problem51-hwxi.dats
	$(ATSCC) -O2 -o $@ problem51-hwxi.dats -lm && ./problem51-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem51-hwxi

###### end of [Makefile] ######
