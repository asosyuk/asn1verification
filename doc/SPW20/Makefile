
IMAGES=VerificationArchitectureDiagram.eps

report.pdf: report.tex report.bib $(IMAGES)
	latexmk --pdf report.tex 

clean:
	latexmk -C
	rm -f *.fdb_latexmk *.fls *.out *.bbl *.blg report.pdf

run: report.pdf
	evince report.pdf

all: report.pdf


