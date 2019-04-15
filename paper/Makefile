.PHONY: paper

paper: 
	pdflatex juliasub-ftfjp-2019.tex

# cleaning

CLEAN_PDF_CMD=find . \( -name "*.pdf" -or -name "*.aux" -or -name "*.log" -or -name "*.out"\
			  -or -name "*.synctex.gz"\
			  -or -name "*.bbl" -or -name "*.blg" -or -name "*.dvi" \) -delete

CLEAN_MINTED_CMD=find . \( -name "_minted*" -type d \) -exec rm -r "{}" \;

clean:
	$(CLEAN_PDF_CMD)
