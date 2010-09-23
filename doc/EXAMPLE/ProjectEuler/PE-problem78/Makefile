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
  problem78-hwxi \

######

problem78-hwxi: problem78-hwxi.dats
	$(ATSCC) -O2 -o $@ problem78-hwxi.dats && ./problem78-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem78-hwxi

###### end of [Makefile] ######
