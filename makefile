TARG = linear-transformations

.PRECIOUS: %.tex %.pdf

all: $(TARG).pdf

%.pdf: %.tex makefile
	pdflatex $*.tex

# --poly is default for lhs2TeX

%.tex: %.lhs macros.tex mine.fmt makefile
	lhs2TeX -o $*.tex $*.lhs

showpdf = open -a Skim.app

see: $(TARG).pdf
	${showpdf} $(TARG).pdf

clean:
	rm $(TARG).{tex,dvi,pdf,aux,bbl,blg}
