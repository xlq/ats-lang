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
  problem13-hwxi \

######

problem13-hwxi: problem13-hwxi.dats
	$(ATSCC) -o $@ problem13-hwxi.dats -lats -lgmp && ./problem13-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem13-hwxi

###### end of [Makefile] ######
