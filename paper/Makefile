.PHONY: paper

paper: 
	pdflatex minijl-ftfjp2019.tex

force:
	pdflatex minijl-ftfjp2019.tex
	bibtex minijl-ftfjp2019
	bibtex minijl-ftfjp2019
	pdflatex minijl-ftfjp2019.tex
	bibtex minijl-ftfjp2019
	pdflatex minijl-ftfjp2019.tex

# cleaning

CLEAN_PDF_CMD=find . \( -name "*.pdf" -or -name "*.aux" -or -name "*.log" -or -name "*.out"\
			  -or -name "*.synctex.gz"\
			  -or -name "*.bbl" -or -name "*.blg" -or -name "*.dvi" \) -delete

CLEAN_MINTED_CMD=find . \( -name "_minted*" -type d \) -exec rm -r "{}" \;

clean:
	$(CLEAN_PDF_CMD)
