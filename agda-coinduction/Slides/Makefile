.PHONY : clean realclean
.PRECIOUS : %.tex

default: lec1-slides.pdf lec2-slides.pdf lec3-slides.pdf

%.pdf : latex/%.tex agda.sty preamble-base.tex
	latexmk --pdf -pdflatex="pdflatex -interaction=nonstopmode -halt-on-error -shell-escape" -use-make $<

%.pdf : %.tex preamble-base.tex
	latexmk --pdf -pdflatex="pdflatex -interaction=nonstopmode -halt-on-error -shell-escape" -use-make $<

latex/%.tex : %.lagda.tex
	agda-2.8.0 --latex $<

clean:
	rm -f *.aux *.log *.out *.ptb *.blg *.fdb_latexmk *.agdai *.fls *.toc *~  *.snm *.vrb *.pyg *.nav

realclean: clean
	rm -f *.glob *.vo *.bbl latex/* *.pdf
	rm -rf _minted-*


