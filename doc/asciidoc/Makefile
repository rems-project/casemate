CASEMATE_LOGO = ../logo/casemate_logo.png

cm_version = $(shell ../../tools/print_version.py)
cm_release_date = $(shell ../../tools/print_version.py --release-date)


all: docinfo.html manual.html

docinfo.html: docinfo.template generate_docinfo.py
	python3 generate_docinfo.py > $@

manual.html: sections/*.adoc manual.adoc docinfo.html
	asciidoctor manual.adoc -r asciidoctor-bibtex -a data-uri -a 'cmversion=$(cm_version)' -a 'cmreleasedate=$(cm_release_date)'

.PHONY: clean
clean:
	-rm manual.html
