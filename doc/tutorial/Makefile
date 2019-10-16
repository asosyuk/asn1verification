COQC = coqc -Q C Clight
COQSRC := $(shell ls *.v)

clean:
	find C -name "*.v" -type f -delete
	find . -name "*.vo" -type f -delete
	find . -name "*.glob" -type f -delete
	find . -name "*.cache" -type f -delete
	find . -name "*.aux" -type f -delete

clight:
	clightgen -normalize C/*.c
	$(COQC) C/*.v
