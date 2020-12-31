VDIR := .
COQARGS := $(strip $(shell cat _CoqProject))

# path to asn1c sources
ASN1C_DIR := ../../asn1c

# files from asn1c/skeletons to be included (space-separated)
ASN1C_FILES := asn_codecs_prim.c INTEGER.c BOOLEAN.c der_encoder.c \
	ber_decoder.c asn_application.c ber_tlv_tag.c ber_tlv_length.c

CALLBACK := callback.c

define skel_path
	$(ASN1C_DIR)/skeletons/$(strip $(1))
endef

default: coq

clight':
	clightgen -normalize -fstruct-passing -flongdouble \
	-I $(ASN1C_DIR)/skeletons \
	$(foreach FILE, $(ASN1C_FILES), $(call skel_path, $(FILE)))

clight'':
	clightgen -normalize -fstruct-passing -flongdouble Clight/dummy.c

clight: clight' clight''
	mv $(foreach FILE, $(ASN1C_FILES), $(call skel_path, $(basename $(FILE))).v) Clight

VFILES := $(shell find . -name "*.v" -type f)

CoqMakefile:
	coq_makefile $(COQARGS) -o CoqMakefile $(VFILES)

coq: CoqMakefile
	$(MAKE) -f CoqMakefile all

clean:
	find . -name "*.vo"    -type f -delete
	find . -name "*.vok"   -type f -delete
	find . -name "*.vos"   -type f -delete
	find . -name "*.aux"   -type f -delete
	find . -name "*.glob"  -type f -delete
	find . -name "*.cache" -type f -delete

distclean: clean
	find ./Clight -name "*.v" -type f -delete
	rm -f CoqMakefile CoqMakefile.conf .coqdeps.d
