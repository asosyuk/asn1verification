
IMAGES=VerificationArchitectureDiagram.png

report.pdf: report.tex report.bib $(IMAGES)
	latexmk --pdf report.tex 

clean:
	rm -f *.fdb_latexmk *.fls *.out *.bbl *.blg report.pdf

run:
	evince report.pdf

all: report.pdf


