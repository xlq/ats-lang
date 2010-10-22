##
##
## TIGERATS: a Tiger compiler written in ATS
##
## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Time: Spring, 2009
##
##

######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all
all:  tigcomp

######

CCFLAGS=
CCFLAGS=-DATSMARCH=x86_32 -g
#CCFLAGS=-DATSMARCH=x86_64 -g
#CCFLAGS=-DATSMARCH=SPIM -g
GCFLAG=-D_ATS_GCATS

######

checkall:: tigcomp cleanall

######

tigcomp: \
  tigerats_main_dats.o \
  error_sats.o error_dats.o \
  stamp_sats.o stamp_dats.o \
  symbol_sats.o symbol_dats.o \
  types_sats.o types_dats.o \
  absyn_sats.o absyn_dats.o \
  fixity_sats.o fixity_dats.o \
  parser_sats.o parser_dats.o \
  tychecker_sats.o tychecker_dats.o \
  interp0_sats.o interp0_dats.o \
  templab_sats.o templab_dats.o \
  irtree_sats.o irtree_dats.o \
  frame_sats.o frame_dats.o \
  translate_sats.o translate_dats.o \
  canonical_sats.o canonical_dats.o \
  interp1_sats.o interp1_dats.o \
  assem_sats.o assem_dats.o \
  codegen_sats.o codegen_dats.o \
  fgnode_sats.o fgnode_dats.o \
  tempset_sats.o tempset_dats.o \
  fgraph_sats.o fgraph_dats.o \
  igraph_sats.o igraph_dats.o \
  liveness_dats.o \
  regalloc_sats.o regalloc_dats.o \
  posloc_sats.o posloc_dats.o \
  tokenize_sats.o tokenize_dats.o \
  parcomb_sats.o parcomb_dats.o \
  funmap_avltree_dats.o \
  hashtable_dats.o \
  linmap_randbst_dats.o \

	$(ATSCC) $(GCFLAG) -o tigcomp \
  tigerats_main_dats.o \
  error_sats.o error_dats.o \
  stamp_sats.o stamp_dats.o \
  symbol_sats.o symbol_dats.o \
  types_sats.o types_dats.o \
  absyn_sats.o absyn_dats.o \
  fixity_sats.o fixity_dats.o \
  parser_sats.o parser_dats.o \
  tychecker_sats.o tychecker_dats.o \
  interp0_sats.o interp0_dats.o \
  templab_sats.o templab_dats.o \
  irtree_sats.o irtree_dats.o \
  frame_sats.o frame_dats.o \
  translate_sats.o translate_dats.o \
  canonical_sats.o canonical_dats.o \
  interp1_sats.o interp1_dats.o \
  assem_sats.o assem_dats.o \
  codegen_sats.o codegen_dats.o \
  fgnode_sats.o fgnode_dats.o \
  tempset_sats.o tempset_dats.o \
  fgraph_sats.o fgraph_dats.o \
  igraph_sats.o igraph_dats.o \
  liveness_dats.o \
  regalloc_sats.o regalloc_dats.o \
  posloc_sats.o posloc_dats.o \
  tokenize_sats.o tokenize_dats.o \
  parcomb_sats.o parcomb_dats.o \
  funmap_avltree_dats.o \
  hashtable_dats.o \
  linmap_randbst_dats.o \

######

tigerats_main_dats.o: tigerats_main.dats
	$(ATSCC) $(CCFLAGS) -c -o tigerats_main_dats.o tigerats_main.dats

######

error_sats.o: error.sats
	$(ATSCC) $(CCFLAGS) -o error_sats.o -c error.sats

error_dats.o: error.dats
	$(ATSCC) $(CCFLAGS) -o error_dats.o -c error.dats

######

stamp_sats.o: stamp.sats
	$(ATSCC) $(CCFLAGS) -o stamp_sats.o -c stamp.sats

stamp_dats.o: stamp.dats
	$(ATSCC) $(CCFLAGS) -o stamp_dats.o -c stamp.dats

######

symbol_sats.o: symbol.sats
	$(ATSCC) $(CCFLAGS) -c -o symbol_sats.o symbol.sats

symbol_dats.o: symbol.dats
	$(ATSCC) $(CCFLAGS) -c -o symbol_dats.o symbol.dats

######

types_sats.o: types.sats
	$(ATSCC) $(CCFLAGS) -c -o types_sats.o types.sats

types_dats.o: types.dats
	$(ATSCC) $(CCFLAGS) -c -o types_dats.o types.dats

######

absyn_sats.o: absyn.sats
	$(ATSCC) $(CCFLAGS) -c -o absyn_sats.o absyn.sats

absyn_dats.o: absyn.dats
	$(ATSCC) $(CCFLAGS) -c -o absyn_dats.o absyn.dats

######

fixity_sats.o: fixity.sats
	$(ATSCC) $(CCFLAGS) -c -o fixity_sats.o fixity.sats

fixity_dats.o: fixity.dats
	$(ATSCC) $(CCFLAGS) -c -o fixity_dats.o fixity.dats

######

parser_sats.o: parser.sats
	$(ATSCC) $(CCFLAGS) -o parser_sats.o -c parser.sats

parser_dats.o: parser.dats
	$(ATSCC) $(CCFLAGS) -IATS PARCOMB -o parser_dats.o -c parser.dats

######

tychecker_sats.o: tychecker.sats
	$(ATSCC) $(CCFLAGS) -o tychecker_sats.o -c tychecker.sats

tychecker_dats.o: tychecker.dats
	$(ATSCC) $(CCFLAGS) -o tychecker_dats.o -c tychecker.dats

######

interp0_sats.o: interp0.sats
	$(ATSCC) $(CCFLAGS) -o interp0_sats.o -c interp0.sats

interp0_dats.o: interp0.dats
	$(ATSCC) $(CCFLAGS) -IATS LIB -o interp0_dats.o -c interp0.dats

######

templab_sats.o: templab.sats
	$(ATSCC) $(CCFLAGS) -o templab_sats.o -c templab.sats

templab_dats.o: templab.dats
	$(ATSCC) $(CCFLAGS) -o templab_dats.o -c templab.dats

######

irtree_sats.o: irtree.sats
	$(ATSCC) $(CCFLAGS) -o irtree_sats.o -c irtree.sats

irtree_dats.o: irtree.dats
	$(ATSCC) $(CCFLAGS) -o irtree_dats.o -c irtree.dats

######

frame_sats.o: frame.sats
	$(ATSCC) $(CCFLAGS) -o frame_sats.o -c frame.sats

frame_dats.o: frame.dats
	$(ATSCC) $(CCFLAGS) -o frame_dats.o -c frame.dats

######

translate_sats.o: translate.sats
	$(ATSCC) $(CCFLAGS) -o translate_sats.o -c translate.sats

translate_dats.o: translate.dats
	$(ATSCC) $(CCFLAGS) -o translate_dats.o -c translate.dats

######

canonical_sats.o: canonical.sats
	$(ATSCC) $(CCFLAGS) -o canonical_sats.o -c canonical.sats

canonical_dats.o: canonical.dats
	$(ATSCC) $(CCFLAGS) -o canonical_dats.o -c canonical.dats

######

interp1_sats.o: interp1.sats
	$(ATSCC) $(CCFLAGS) -o interp1_sats.o -c interp1.sats

interp1_dats.o: interp1.dats
	$(ATSCC) $(CCFLAGS) -IATS LIB -o interp1_dats.o -c interp1.dats

######

assem_sats.o: assem.sats
	$(ATSCC) $(CCFLAGS) -o assem_sats.o -c assem.sats

assem_dats.o: assem.dats
	$(ATSCC) $(CCFLAGS) -o assem_dats.o -c assem.dats

######

codegen_sats.o: codegen.sats
	$(ATSCC) $(CCFLAGS) -o codegen_sats.o -c codegen.sats

codegen_dats.o: codegen.dats \
        codegen_spim.dats codegen_x86_32.dats
	$(ATSCC) $(CCFLAGS) -o codegen_dats.o -c codegen.dats

######

fgnode_sats.o: fgnode.sats
	$(ATSCC) $(CCFLAGS) -o fgnode_sats.o -c fgnode.sats

fgnode_dats.o: fgnode.dats
	$(ATSCC) $(CCFLAGS) -o fgnode_dats.o -c fgnode.dats

######

tempset_sats.o: tempset.sats
	$(ATSCC) $(CCFLAGS) -o tempset_sats.o -c tempset.sats

tempset_dats.o: tempset.dats
	$(ATSCC) $(CCFLAGS) -o tempset_dats.o -c tempset.dats

######

fgraph_sats.o: fgraph.sats
	$(ATSCC) $(CCFLAGS) -o fgraph_sats.o -c fgraph.sats

fgraph_dats.o: fgraph.dats
	$(ATSCC) $(CCFLAGS) -o fgraph_dats.o -c fgraph.dats

######

igraph_sats.o: igraph.sats
	$(ATSCC) $(CCFLAGS) -o igraph_sats.o -c igraph.sats

igraph_dats.o: igraph.dats
	$(ATSCC) $(CCFLAGS) -o igraph_dats.o -c igraph.dats

######

liveness_dats.o: liveness.dats
	$(ATSCC) $(CCFLAGS) -o liveness_dats.o -c liveness.dats

######

regalloc_sats.o: regalloc.sats
	$(ATSCC) $(CCFLAGS) -o regalloc_sats.o -c regalloc.sats

regalloc_dats.o: regalloc.dats
	$(ATSCC) $(CCFLAGS) -o regalloc_dats.o -c regalloc.dats

######

posloc_sats.o: PARCOMB/posloc.sats
	$(ATSCC) $(CCFLAGS) -c -o posloc_sats.o PARCOMB/posloc.sats

posloc_dats.o: PARCOMB/posloc.dats
	$(ATSCC) $(CCFLAGS) -IATS PARCOMB -c -o posloc_dats.o PARCOMB/posloc.dats

parcomb_sats.o: PARCOMB/parcomb.sats
	$(ATSCC) $(CCFLAGS) -c -o parcomb_sats.o PARCOMB/parcomb.sats

parcomb_dats.o: PARCOMB/parcomb.dats
	$(ATSCC) $(CCFLAGS) -IATS PARCOMB -c -o parcomb_dats.o PARCOMB/parcomb.dats

tokenize_sats.o: PARCOMB/tokenize.sats
	$(ATSCC) $(CCFLAGS) -IATS PARCOMB -c -o tokenize_sats.o PARCOMB/tokenize.sats

tokenize_dats.o: PARCOMB/tokenize.dats
	$(ATSCC) $(CCFLAGS) -IATS PARCOMB -c -o tokenize_dats.o PARCOMB/tokenize.dats

######

funmap_avltree_dats.o: LIB/funmap_avltree.dats
	$(ATSCC) $(CCFLAGS) -IATS LIB -c -o funmap_avltree_dats.o LIB/funmap_avltree.dats

######

hashtable_dats.o: LIB/hashtable.dats
	$(ATSCC) $(CCFLAGS) -IATS LIB -c -o hashtable_dats.o LIB/hashtable.dats

######

linmap_randbst_dats.o: LIB/linmap_randbst.dats
	$(ATSCC) $(CCFLAGS) -IATS LIB -c -o linmap_randbst_dats.o LIB/linmap_randbst.dats

######

xref::
	$(ATSOPT) --posmark_xref=XREF \
          -d $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
	$(ATSOPT) --posmark_xref=XREF \
          -d tigerats_main.dats > tigerats_main_dats.html
	$(ATSOPT) --posmark_xref=XREF -d error.dats > error_dats.html
	$(ATSOPT) --posmark_xref=XREF -d stamp.dats > stamp_dats.html
	$(ATSOPT) --posmark_xref=XREF -d symbol.dats > symbol_dats.html
	$(ATSOPT) --posmark_xref=XREF -d types.dats > types_dats.html
	$(ATSOPT) -IATS PARCOMB -IATS LIB \
          --posmark_xref=XREF -d absyn.dats > absyn_dats.html
	$(ATSOPT) -IATS PARCOMB -IATS LIB \
	  --posmark_xref=XREF -d fixity.dats > fixity_dats.html
	$(ATSOPT) -IATS PARCOMB -IATS LIB \
	  --posmark_xref=XREF -d parser.dats > parser_dats.html
	$(ATSOPT) -IATS PARCOMB -IATS LIB \
	  --posmark_xref=XREF -d tychecker.dats > tychecker_dats.html
	$(ATSOPT) --posmark_xref=XREF -d interp0.dats > interp0_dats.html
	$(ATSOPT) --posmark_xref=XREF -d templab.dats > templab_dats.html
	$(ATSOPT) --posmark_xref=XREF -d irtree.dats > irtree_dats.html
	$(ATSOPT) --posmark_xref=XREF -d frame.dats > frame_dats.html
	$(ATSOPT) --posmark_xref=XREF -d translate.dats > translate_dats.html
	$(ATSOPT) --posmark_xref=XREF -d canonical.dats > canonical_dats.html
	$(ATSOPT) --posmark_xref=XREF -d interp1.dats > interp1_dats.html
	$(ATSOPT) --posmark_xref=XREF -d assem.dats > assem_dats.html
	$(ATSOPT) --posmark_xref=XREF -d codegen.dats > codegen_dats.html
	$(ATSOPT) --posmark_xref=XREF -d fgnode.dats > fgnode_dats.html
	$(ATSOPT) --posmark_xref=XREF -d tempset.dats > tempset_dats.html
	$(ATSOPT) --posmark_xref=XREF -d fgraph.dats > fgraph_dats.html
	$(ATSOPT) --posmark_xref=XREF -d igraph.dats > igraph_dats.html
	$(ATSOPT) --posmark_xref=XREF -d liveness.dats > liveness_dats.html
	$(ATSOPT) --posmark_xref=XREF -d regalloc.dats > regalloc_dats.html

######

chmod::
	chmod 644 Makefile
	chmod 644 tiger_prelude.c tiger_prelude_spim.s
	chmod 644 *.?ats
	chmod 644 *_?ats.html
	cd XREF; chmod 644 *.html

######

tar:: cleanall
	cp tigerats_main.dats Tigerats
	cp error.sats error.dats Tigerats
	cp fixity.sats fixity.dats Tigerats
	cp stamp.sats stamp.dats Tigerats
	cp symbol.sats symbol.dats Tigerats
	cp types.sats types.dats Tigerats
	cp absyn.sats absyn.dats Tigerats
	cp fixity.sats fixity.dats Tigerats
	cp parser.sats parser.dats Tigerats
	cp tychecker.sats tychecker.dats Tigerats
	cp interp0.sats interp0.dats Tigerats
	cp templab.sats templab.dats Tigerats
	cp irtree.sats irtree.dats Tigerats
	cp frame.sats frame.dats Tigerats
	cp translate.sats translate.dats Tigerats
	cp canonical.sats canonical.dats Tigerats
	cp interp1.sats interp1.dats Tigerats
	cp assem.sats assem.dats Tigerats
	cp codegen.sats codegen.dats Tigerats
	cp codegen_spim.dats codegen_x86_32.dats Tigerats
	cp fgnode.sats fgnode.dats Tigerats
	cp tempset.sats tempset.dats Tigerats
	cp fgraph.sats fgraph.dats Tigerats
	cp igraph.sats igraph.dats Tigerats
	cp liveness.dats Tigerats
	cp regalloc.sats regalloc.dats Tigerats
	cp PARCOMB/posloc.sats PARCOMB/posloc.dats Tigerats/PARCOMB
	cp PARCOMB/tokenize.sats PARCOMB/tokenize.dats Tigerats/PARCOMB
	cp PARCOMB/parcomb.sats PARCOMB/parcomb.dats Tigerats/PARCOMB
	cp LIB/funmap_avltree.dats Tigerats/LIB
	cp LIB/hashtable.dats Tigerats/LIB
	cp LIB/linmap_randbst.dats Tigerats/LIB
	cp Makefile_tigerats Tigerats/Makefile
	cp params.hats Tigerats
	cp tiger_prelude.c Tigerats
	cp tiger_prelude_spim.s Tigerats
	cp EXAMPLE/*.tig Tigerats/EXAMPLE
	cp EXAMPLE/Makefile Tigerats/EXAMPLE
	tar vcfz Tigerats.tar.gz Tigerats/

######

clean::
	rm -f *~
	rm -f *_sats.c *_dats.c
	rm -f *_sats.o *_dats.o

cleanall: clean
	rm -f tigcomp
	rm -f *_?ats.html */*_?ats.html
	rm -f XREF/*.html

######

lines::
	wc -l *.?ats

###### end of [Makefile] ######
