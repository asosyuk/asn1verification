COQC = coqc -Q C Clight
COQSRC := $(shell ls *.v)

clean:
	rm C/*.v
	find . -name "*.vo" -type f -delete
	find . -name "*.glob" -type f -delete
	find . -name "*.cache" -type f -delete
	find . -name "*.aux" -type f -delete

clight:
	clightgen C/*.c
	$(COQC) C/*.v

coq:
	$(COQC) sum.v
	$(COQC) max.v
	$(COQC) pow2.v
	$(COQC) strlen.v
