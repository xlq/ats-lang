ats-main::
	scp ats-main.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

file-inclusion::
	scp file-inclusion.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

compilation::
	scp compilation.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

fixity::
	scp fixity.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

overloading::
	scp overloading.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

datatypes::
	scp datatypes.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

dataviewtypes::
	scp dataviewtypes.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

pattern-matching::
	scp pattern-matching.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

call-by-reference::
	scp call-by-reference.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

templates::
	scp templates.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

lists::
	scp lists.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

references::
	scp references.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

arrays-and-matrices::
	scp arrays-and-matrices.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

linear-arrays::
	scp linear-arrays.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

tail-recursive-functions::
	scp tail-recursive-functions.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

lazy-evaluation::
	scp lazy-evaluation.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

variadicity::
	scp variadicity.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

function-or-closure::
	scp function-or-closure.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

val-and-var::
	scp val-and-var.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

input-and-output::
	scp input-and-output.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

######

typecheck::
	atscc  arrays-and-matrices.dats
	atscc  ATS-and-C.dats
	atscc  ats-main.dats
	atscc  basics.dats -lm
	atscc  dataprops.dats
	atscc  datatypes.dats
	atscc  dataviews.dats
	atscc  dataviewtypes.dats
	atscc  functions-with-variable-arguments.dats
	atscc  lazy-evaluation.dats
	atscc  pattern-matching
	atscc  programming-with-theorem-proving.dats
	atscc  references.dats
	atscc  input-and-output.dats
	atscc  tail-recursive-functions.dats
	atscc  termination-metrics.dats

######

clean::
	rm -f a.out *_dats.c *_sats.c *~

cleanall: clean; rm -f *_?ats.html

######
