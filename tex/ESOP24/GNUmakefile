.PHONY: paper
paper: BiSig.pdf

BiSig.pdf: *.tex agda.fmt *.lhs
	latexmk -pdf BiSig

.PHONY: watch
watch: *.tex agda.fmt *.lhs
	latexmk -pdf -pvc BiSig

.PHONY: clean
clean:
	latexmk -CA
	rm S7-formalisation.tex agda-lhs2tex.sty
