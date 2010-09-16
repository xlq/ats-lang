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
  problem24-hwxi \

######

problem24-hwxi: problem24-hwxi.dats
	$(ATSCC) -O2 -o $@ problem24-hwxi.dats && ./problem24-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem24-hwxi

###### end of [Makefile] ######
