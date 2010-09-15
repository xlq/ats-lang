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
  problem39-hwxi \

######

problem39-hwxi: problem39-hwxi.dats
	$(ATSCC) -O2 -o $@ problem39-hwxi.dats && ./problem39-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem39-hwxi

###### end of [Makefile] ######
