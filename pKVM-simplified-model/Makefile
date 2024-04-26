all :
	dune build _build/default/simplified.install --display short

sm-test:
	dune exe parser

sm-coverage:
	dune exe parser --instrument-with bisect_ppx --force && bisect-ppx-report html

clean:
	dune clean
	rm -rf _coverage *.coverage

.PHONY : all sm-test sm-coverage
