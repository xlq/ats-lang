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
  problem31-hwxi \

######

problem31-hwxi: problem31-hwxi.dats
	$(ATSCC) -O3 -o $@ problem31-hwxi.dats && ./problem31-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem31-hwxi

###### end of [Makefile] ######
