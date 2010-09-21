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
  problem80-hwxi \

######

problem80-hwxi: problem80-hwxi.dats
	$(ATSCC) -o $@ problem80-hwxi.dats -lats -lgmp -lm && ./problem80-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem80-hwxi

###### end of [Makefile] ######
