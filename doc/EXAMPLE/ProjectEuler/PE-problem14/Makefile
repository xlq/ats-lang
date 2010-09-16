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
  problem14-hwxi \

######

problem14-hwxi: problem14-hwxi.dats
	$(ATSCC) -o $@ problem14-hwxi.dats -lats -lgmp && ./problem14-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem14-hwxi

###### end of [Makefile] ######
