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
  frame_sats.o frame_x86_dats.o \
  translate_sats.o translate_dats.o \
  canonical_sats.o canonical_dats.o \
  interp1_sats.o interp1_dats.o \
  posloc_sats.o posloc_dats.o \
  tokenize_sats.o tokenize_dats.o \
  parcomb_sats.o parcomb_dats.o \
  hashtable_dats.o \
  funmap_avltree_dats.o \


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
  frame_sats.o frame_x86_dats.o \
  translate_sats.o translate_dats.o \
  canonical_sats.o canonical_dats.o \
  interp1_sats.o interp1_dats.o \
  posloc_sats.o posloc_dats.o \
  tokenize_sats.o tokenize_dats.o \
  parcomb_sats.o parcomb_dats.o \
  hashtable_dats.o \
  funmap_avltree_dats.o \

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
	atscc $(CCFLAGS) -IATS PARCOMB -c -o fixity_sats.o fixity.sats

fixity_dats.o: fixity.dats
	atscc $(CCFLAGS) -IATS PARCOMB -c -o fixity_dats.o fixity.dats

######

parser_sats.o: parser.sats
	atscc $(CCFLAGS) -o parser_sats.o -c parser.sats

parser_dats.o: parser.dats
	atscc $(CCFLAGS) -IATS PARCOMB -o parser_dats.o -c parser.dats

######

tychecker_sats.o: tychecker.sats
	atscc $(CCFLAGS) -o tychecker_sats.o -c tychecker.sats

tychecker_dats.o: tychecker.dats
	atscc $(CCFLAGS) -IATS PARCOMB -o tychecker_dats.o -c tychecker.dats

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

frame_x86_dats.o: frame_x86.dats
	atscc $(CCFLAGS) -o frame_x86_dats.o -c frame_x86.dats

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

hashtable_dats.o: LIB/hashtable.dats
	atscc $(CCFLAGS) -IATS LIB -c -o hashtable_dats.o LIB/hashtable.dats

######

funmap_avltree_dats.o: LIB/funmap_avltree.dats
	atscc $(CCFLAGS) -IATS LIB -c -o funmap_avltree_dats.o LIB/funmap_avltree.dats

######

html::
	atsopt -IATS PARCOMB -IATS LIB \
          --posmark_html_xref -d *.dats -s *.sats
	cd LIB; atsopt --posmark_html_xref -d *.dats
	cd PARCOMB; atsopt --posmark_html_xref -d *.dats -s *.sats

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

######

lines::
	wc -l *.?ats

###### end of [Makefile] ######
