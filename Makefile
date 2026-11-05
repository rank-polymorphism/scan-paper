LAGDA := related array vector initial combinators performance

SRC := paper.tex \
       intro.tex \
			 conclusions.tex \
       paper.bib \
       $(LAGDA:%=latex/%.tex)

AGDA := agda

all: paper.pdf docs


.PHONY: all clean agda docs

# Stand-alone Agda modules extracted from the literate sources (see agda/README.md).
# The other files in agda/ (StabilityNoRewrite.agda, README.md, the library
# file) are written by hand.
AGDA_GEN := $(addprefix agda/,$(addsuffix .agda,\
              Arrays Initial Vectors Combinators Reshaping Stability Performance Everything))

$(AGDA_GEN) &: $(LAGDA:%=%.lagda) tools/extract-agda.py
	python3 tools/extract-agda.py

agda: $(AGDA_GEN)
	cd agda && $(AGDA) Everything.agda

# Web page with the paper and the Agda code, published at
# https://rank-polymorphism.github.io/scan-paper/ (see docs/index.html).
docs: docs/paper.pdf docs/agda/Everything.html

docs/paper.pdf: paper.pdf
	cp $< $@

docs/agda/Everything.html: $(AGDA_GEN) agda/StabilityNoRewrite.agda
	cd agda && $(AGDA) --html --highlight-occurrences --html-dir=../docs/agda Everything.agda

latex/%.tex : %.lagda
	$(AGDA) -i. --latex $< #--only-scope-checking $<

paper.pdf: $(SRC)
	TEXINPUTS=./latex:$$TEXINPUTS latexmk -pdf -f -pdflatex='pdflatex -halt-on-error' $<
	touch $@

clean:
	latexmk -c
	$(RM) *.ptb *.bbl paper.pdf

cleangen:
	$(RM) $(AGDA_GEN) docs/paper.pdf
	$(RM) -r docs/agda agda/_build
