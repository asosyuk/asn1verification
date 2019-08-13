VDIR := .
VFILES := $(shell find . -name "*.v" -type f)
COQARGS := $(strip $(shell cat _CoqProject))

# path to asn1c sources
ASN1C_DIR := ../../asn1c

# files from asn1c/skeletons to be included (space-separated)
ASN1C_FILES := INTEGER.c

# generate [.v] clight
# from a [.c] in [asn1c/skeletons]
# and put it under [./Clight]
define generate_clight

	clightgen -normalize -fstruct-passing -flongdouble \
	-I $(ASN1C_DIR)/skeletons                          \
	$(ASN1C_DIR)/skeletons/$(strip $(1))               \
	-o ./Clight/$(basename $(1)).v

endef


default: coq

clight:
	$(foreach FILE, $(ASN1C_FILES), $(call generate_clight, $(FILE)))

CoqMakefile:
	coq_makefile $(COQARGS) -o CoqMakefile $(VFILES)

coq: CoqMakefile
	$(MAKE) -f CoqMakefile all

clean:
	find . -name "*.vo"    -type f -not -path "./Clight/*" -delete
	find . -name "*.aux"   -type f -not -path "./Clight/*" -delete
	find . -name "*.glob"  -type f -not -path "./Clight/*" -delete
	find . -name "*.cache" -type f -not -path "./Clight/*" -delete

distclean:
	find . -name "*.vo"    -type f -delete
	find . -name "*.vo"    -type f -delete
	find . -name "*.aux"   -type f -delete
	find . -name "*.glob"  -type f -delete
	find . -name "*.cache" -type f -delete
	find ./Clight -name "*.v"     -type f -delete
	rm -f CoqMakefile CoqMakefile.conf .coqdeps.d
