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
  problem50-hwxi \

######

problem50-hwxi: problem50-hwxi.dats
	$(ATSCC) -o $@ problem50-hwxi.dats && ./problem50-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem50-hwxi

###### end of [Makefile] ######
