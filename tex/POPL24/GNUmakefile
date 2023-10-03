.PHONY: NDGP
paper: BiSig.pdf

BiSig.pdf: *.tex agda.fmt *.lhs
	latexmk -pdf BiSig

.PHONY: watch
watch: tex
	latexmk -pdf -pvc BiSig

.PHONY: clean
clean:
	latexmk -CA
	rm sec6-formalisation.tex agda-lhs2tex.sty
