##
##
## a Tiger compiler written in ATS
##
## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Time: Spring, 2009
##
##

######

CCFLAGS=
CCFLAGS=-g
GCFLAG=-D_ATS_GCATS

######

comptig: \
  tiger_main_dats.o \
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
  funarray_dats.o \
  funmap_avltree_dats.o \
  hashtable_dats.o \
  linmap_randbst_dats.o \


	atscc $(GCFLAG) -o comptig \
  tiger_main_dats.o \
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
  funarray_dats.o \
  funmap_avltree_dats.o \
  hashtable_dats.o \
  linmap_randbst_dats.o \

######

tiger_main_dats.o: tiger_main.dats
	atscc $(CCFLAGS) -c -o tiger_main_dats.o tiger_main.dats

######

error_sats.o: error.sats
	atscc $(CCFLAGS) -o error_sats.o -c error.sats

error_dats.o: error.dats
	atscc $(CCFLAGS) -o error_dats.o -c error.dats

######

stamp_sats.o: stamp.sats
	atscc $(CCFLAGS) -o stamp_sats.o -c stamp.sats

stamp_dats.o: stamp.dats
	atscc $(CCFLAGS) -o stamp_dats.o -c stamp.dats

######

symbol_sats.o: symbol.sats
	atscc $(CCFLAGS) -c -o symbol_sats.o symbol.sats

symbol_dats.o: symbol.dats
	atscc $(CCFLAGS) -c -o symbol_dats.o symbol.dats

######

types_sats.o: types.sats
	atscc $(CCFLAGS) -c -o types_sats.o types.sats

types_dats.o: types.dats
	atscc $(CCFLAGS) -c -o types_dats.o types.dats

######

absyn_sats.o: absyn.sats
	atscc $(CCFLAGS) -c -o absyn_sats.o absyn.sats

absyn_dats.o: absyn.dats
	atscc $(CCFLAGS) -c -o absyn_dats.o absyn.dats

######

fixity_sats.o: fixity.sats
	atscc $(CCFLAGS) -c -o fixity_sats.o fixity.sats

fixity_dats.o: fixity.dats
	atscc $(CCFLAGS) -c -o fixity_dats.o fixity.dats

######

parser_sats.o: parser.sats
	atscc $(CCFLAGS) -o parser_sats.o -c parser.sats

parser_dats.o: parser.dats
	atscc $(CCFLAGS) -IATS PARCOMB -o parser_dats.o -c parser.dats

######

tychecker_sats.o: tychecker.sats
	atscc $(CCFLAGS) -o tychecker_sats.o -c tychecker.sats

tychecker_dats.o: tychecker.dats
	atscc $(CCFLAGS) -o tychecker_dats.o -c tychecker.dats

######

interp0_sats.o: interp0.sats
	atscc $(CCFLAGS) -o interp0_sats.o -c interp0.sats

interp0_dats.o: interp0.dats
	atscc $(CCFLAGS) -IATS LIB -o interp0_dats.o -c interp0.dats

######

templab_sats.o: templab.sats
	atscc $(CCFLAGS) -o templab_sats.o -c templab.sats

templab_dats.o: templab.dats
	atscc $(CCFLAGS) -o templab_dats.o -c templab.dats

######

irtree_sats.o: irtree.sats
	atscc $(CCFLAGS) -o irtree_sats.o -c irtree.sats

irtree_dats.o: irtree.dats
	atscc $(CCFLAGS) -o irtree_dats.o -c irtree.dats

######

frame_sats.o: frame.sats
	atscc $(CCFLAGS) -o frame_sats.o -c frame.sats

frame_dats.o: frame.dats
	atscc $(CCFLAGS) -o frame_dats.o -c frame.dats

######

translate_sats.o: translate.sats
	atscc $(CCFLAGS) -o translate_sats.o -c translate.sats

translate_dats.o: translate.dats
	atscc $(CCFLAGS) -o translate_dats.o -c translate.dats

######

canonical_sats.o: canonical.sats
	atscc $(CCFLAGS) -o canonical_sats.o -c canonical.sats

canonical_dats.o: canonical.dats
	atscc $(CCFLAGS) -o canonical_dats.o -c canonical.dats

######

interp1_sats.o: interp1.sats
	atscc $(CCFLAGS) -o interp1_sats.o -c interp1.sats

interp1_dats.o: interp1.dats
	atscc $(CCFLAGS) -IATS LIB -o interp1_dats.o -c interp1.dats

######

assem_sats.o: assem.sats
	atscc $(CCFLAGS) -o assem_sats.o -c assem.sats

assem_dats.o: assem.dats
	atscc $(CCFLAGS) -o assem_dats.o -c assem.dats

######

codegen_sats.o: codegen.sats
	atscc $(CCFLAGS) -o codegen_sats.o -c codegen.sats

codegen_dats.o: codegen.dats \
        codegen_mips.dats codegen_x86_32.dats
	atscc $(CCFLAGS) -o codegen_dats.o -c codegen.dats

######

fgnode_sats.o: fgnode.sats
	atscc $(CCFLAGS) -o fgnode_sats.o -c fgnode.sats

fgnode_dats.o: fgnode.dats
	atscc $(CCFLAGS) -o fgnode_dats.o -c fgnode.dats

######

tempset_sats.o: tempset.sats
	atscc $(CCFLAGS) -o tempset_sats.o -c tempset.sats

tempset_dats.o: tempset.dats
	atscc $(CCFLAGS) -o tempset_dats.o -c tempset.dats

######

fgraph_sats.o: fgraph.sats
	atscc $(CCFLAGS) -o fgraph_sats.o -c fgraph.sats

fgraph_dats.o: fgraph.dats
	atscc $(CCFLAGS) -o fgraph_dats.o -c fgraph.dats

######

igraph_sats.o: igraph.sats
	atscc $(CCFLAGS) -o igraph_sats.o -c igraph.sats

igraph_dats.o: igraph.dats
	atscc $(CCFLAGS) -o igraph_dats.o -c igraph.dats

######

liveness_dats.o: liveness.dats
	atscc $(CCFLAGS) -o liveness_dats.o -c liveness.dats

######

regalloc_sats.o: regalloc.sats
	atscc $(CCFLAGS) -o regalloc_sats.o -c regalloc.sats

regalloc_dats.o: regalloc.dats
	atscc $(CCFLAGS) -o regalloc_dats.o -c regalloc.dats

######

posloc_sats.o: PARCOMB/posloc.sats
	atscc $(CCFLAGS) -c -o posloc_sats.o PARCOMB/posloc.sats

posloc_dats.o: PARCOMB/posloc.dats
	atscc $(CCFLAGS) -IATS PARCOMB -c -o posloc_dats.o PARCOMB/posloc.dats

parcomb_sats.o: PARCOMB/parcomb.sats
	atscc $(CCFLAGS) -c -o parcomb_sats.o PARCOMB/parcomb.sats

parcomb_dats.o: PARCOMB/parcomb.dats
	atscc $(CCFLAGS) -IATS PARCOMB -c -o parcomb_dats.o PARCOMB/parcomb.dats

tokenize_sats.o: PARCOMB/tokenize.sats
	atscc $(CCFLAGS) -IATS PARCOMB -c -o tokenize_sats.o PARCOMB/tokenize.sats

tokenize_dats.o: PARCOMB/tokenize.dats
	atscc $(CCFLAGS) -IATS PARCOMB -c -o tokenize_dats.o PARCOMB/tokenize.dats

######

funarray_dats.o: LIB/funarray.dats
	atscc $(CCFLAGS) -IATS LIB -c -o funarray_dats.o LIB/funarray.dats

######

funmap_avltree_dats.o: LIB/funmap_avltree.dats
	atscc $(CCFLAGS) -IATS LIB -c -o funmap_avltree_dats.o LIB/funmap_avltree.dats

######

hashtable_dats.o: LIB/hashtable.dats
	atscc $(CCFLAGS) -IATS LIB -c -o hashtable_dats.o LIB/hashtable.dats

######

linmap_randbst_dats.o: LIB/linmap_randbst.dats
	atscc $(CCFLAGS) -IATS LIB -c -o linmap_randbst_dats.o LIB/linmap_randbst.dats

######

ATSOPT=$(ATSHOME)/bin/atsopt

xref::
	$(ATSOPT) --posmark_xref=XREF \
          -d tiger_main.dats > tiger_main_dats.html
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
	chmod 644 *_?ats.html
	cd LIB; chmod 644 *_?ats.html
	cd PARCOMB; chmod 644 *_?ats.html

######

tar:: cleanall
	cd ..; tar vcfz Tiger.tar.gz Tiger/

update:: tar
	mv ../Tiger.tar.gz $(CS525)/code/; cd $(CS525)/code/; tar vxfz Tiger.tar.gz

######

clean::
	rm -f *~
	rm -f *_sats.c *_dats.c
	rm -f *_sats.o *_dats.o

cleanall: clean
	rm -f comptig
	rm -f *_?ats.html */*_?ats.html
	rm -f XREF/*.html

######

lines::
	wc -l *.?ats

###### end of [Makefile] ######
