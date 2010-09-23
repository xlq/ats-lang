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
  problem120-hwxi \

######

problem120-hwxi: problem120-hwxi.dats
	$(ATSCC) -O2 -o $@ problem120-hwxi.dats && ./problem120-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem120-hwxi

###### end of [Makefile] ######
