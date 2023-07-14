all:
	cp README.tex Matematicas_en_Lean4.tex ; \
	xelatex --shell-escape Matematicas_en_Lean4 ; \
	rm *.mtc[1-9] *.mtc ; \
