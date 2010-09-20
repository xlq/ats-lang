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
  problem42-hwxi \

######

problem42-hwxi: problem42-hwxi.dats
	$(ATSCC) -o $@ problem42-hwxi.dats -lm && ./problem42-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem42-hwxi

###### end of [Makefile] ######
