all :
	dune build _build/default/casemate.install --display short

# cm-test:
# 	dune exe parser ${trace}
#
# cm-coverage:
# 	dune exe parser --instrument-with bisect_ppx --force ${trace} && bisect-ppx-report html
#
clean:
	dune clean
	rm -rf _coverage *.coverage

.PHONY : all cm-test
