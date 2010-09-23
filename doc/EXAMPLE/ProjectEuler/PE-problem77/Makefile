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
  problem77-hwxi \

######

problem77-hwxi: problem77-hwxi.dats
	$(ATSCC) -O2 -o $@ problem77-hwxi.dats -lm && ./problem77-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem77-hwxi

###### end of [Makefile] ######
