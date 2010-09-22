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
  problem73-hwxi \

######

problem73-hwxi: problem73-hwxi.dats
	$(ATSCC) -O2 -o $@ problem73-hwxi.dats && ./problem73-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem73-hwxi

###### end of [Makefile] ######
