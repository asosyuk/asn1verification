#!/bin/sh

ASN1C_DIR=../../asn1c

# generate [.v] clight
# from a [.c] in [asn1c/skeletons]
# and put it under [./Clight]
generate_clight() {

  INP=$1
  OUTP=${INP%%.*}.v

  clightgen -normalize -fstruct-passing -flongdouble \
            -I $ASN1C_DIR/skeletons                  \
            $ASN1C_DIR/skeletons/$INP                \
            -o ./Clight/$OUTP

}

# generate required ASTs
generate_clight INTEGER.c

# generate a makefile for all .v files
coq_makefile -f _CoqProject -o Makefile $(find . -type f -name "*.v")
