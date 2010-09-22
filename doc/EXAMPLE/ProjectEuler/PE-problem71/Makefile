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
  problem71-hwxi \

######

problem71-hwxi: problem71-hwxi.dats
	$(ATSCC) -O2 -o $@ problem71-hwxi.dats && ./problem71-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem71-hwxi

###### end of [Makefile] ######
