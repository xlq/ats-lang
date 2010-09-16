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
  problem26-hwxi \

######

problem26-hwxi: problem26-hwxi.dats
	$(ATSCC) -o $@ problem26-hwxi.dats && ./problem26-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem26-hwxi

###### end of [Makefile] ######
