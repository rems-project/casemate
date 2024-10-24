all : casemate_logo.svg casemate_logo.png

casemate_logo.pdf : casemate_logo.tex
	pdflatex $^

casemate_logo.svg : casemate_logo.pdf
	inkscape $^ --export-plain-svg -o $@

casemate_logo.png : casemate_logo.pdf
	inkscape $^ --export-type="png" -o $@
