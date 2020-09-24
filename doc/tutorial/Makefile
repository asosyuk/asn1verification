VFILES := $(shell find . -name "*.v" -type f)
COQARGS := $(strip $(shell cat _CoqProject))

clean:
	find C -name "*.v" -type f -delete
	find . -name "*.vo" -type f -delete
	find . -name "*.glob" -type f -delete
	find . -name "*.cache" -type f -delete
	find . -name "*.aux" -type f -delete
	find . -name "CoqMakefile" -type f -delete

CoqMakefile:
	coq_makefile $(COQARGS) -o CoqMakefile $(VFILES)

coq: CoqMakefile
	$(MAKE) -f CoqMakefile all

clight:
	clightgen -normalize C/*.c
