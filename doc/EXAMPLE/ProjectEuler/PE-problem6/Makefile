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
  problem6-hwxi \
  problem6-hwxi2 \

######

problem6-hwxi: problem6-hwxi.dats
	$(ATSCC) -o $@ problem6-hwxi.dats && ./problem6-hwxi
problem6-hwxi2: problem6-hwxi2.dats
	$(ATSCC) -o $@ problem6-hwxi2.dats && ./problem6-hwxi2

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem6-hwxi
	rm -f problem6-hwxi2

###### end of [Makefile] ######
