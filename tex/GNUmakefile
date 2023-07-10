.PHONY: NDGP
paper: BiSig.pdf

BiSig.pdf: *.tex agda.fmt *.lhs
	latexmk -pdf -auxdir=aux BiSig

.PHONY: watch
watch: tex
	latexmk -pdf -pvc -auxdir=aux BiSig

.PHONY: clean
clean:
	latexmk -CA -auxdir=aux
	rm sec6-formalisation.tex agda-lhs2tex.sty
