all: manual.html

.PHONY: FORCE

asciidoc/manual.html: FORCE
	@$(MAKE) --no-print-directory -C asciidoc/ manual.html

manual.html: asciidoc/manual.html
	cp $< $@

.PHONY: clean
clean:
	-rm manual.html
