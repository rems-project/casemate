CASEMATE_LOGO = ../logo/casemate_logo.png

all: docinfo.html manual.html

docinfo.html: docinfo.template
	python -c 'import pathlib, base64; print(pathlib.Path("$<").read_text().replace("LOGO_B64_SRC", base64.b64encode(pathlib.Path("../logo/casemate_logo.png").read_bytes()).decode()))' > $@

manual.html: sections/*.adoc manual.adoc docinfo.html
	asciidoctor manual.adoc -r asciidoctor-bibtex -a data-uri

.PHONY: clean
clean:
	-rm manual.html
