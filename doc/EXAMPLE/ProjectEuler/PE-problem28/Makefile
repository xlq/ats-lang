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
  problem28-hwxi \

######

problem28-hwxi: problem28-hwxi.dats
	$(ATSCC) -O2 -o $@ problem28-hwxi.dats && ./problem28-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem28-hwxi

###### end of [Makefile] ######
