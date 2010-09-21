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
  problem55-hwxi \

######

problem55-hwxi: problem55-hwxi.dats
	$(ATSCC) -o $@ problem55-hwxi.dats -lats -lgmp && ./problem55-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem55-hwxi

###### end of [Makefile] ######
