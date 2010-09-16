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
  problem12-hwxi \

######

problem12-hwxi: problem12-hwxi.dats
	$(ATSCC) -O2 -o $@ problem12-hwxi.dats && ./problem12-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem12-hwxi

###### end of [Makefile] ######
