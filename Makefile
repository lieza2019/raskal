DVI2PDF = dvipdfmx
TEX = platex --kanji=euc

ras_spec.pdf: ras_spec.dvi
	$(DVI2PDF) $<

ras_spec.dvi: ras_spec.tex
	$(TEX) $<
	$(TEX) $<


.PHONY: clean
clean:
	-$(RM) *.log
	-$(RM) *.aux
	-$(RM) *.dvi
	-$(RM) *~
	-$(RM) #*


.PHONY: purge
purge:
	-$(RM) *.log
	-$(RM) *.aux
	-$(RM) *.dvi
	-$(RM) *.pdf
	-$(RM) *~
	-$(RM) #*
