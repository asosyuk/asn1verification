# asn1verification
Verification of the [asn1c](https://github.com/vlm/asn1c) compiler in Coq using compcert

# asn1verification using vst

## Dependencies

## clightgen installation

``` shell
    opam pin add coq 8.11.0 --yes && opam install menhir --yes && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev && \
    opam install coq-compcert.3.7 --yes
```
## vst installation

``` shell
	opam install coq-struct-tact coq-ext-lib --yes
    opam install coq-vst.2.6 --yes
```

## Building asn1verification project

``` shell
cd src
make clight 
make 
```

## `make` targets
* `clight` - generate Clight files from C sources (generated .v files are not compiled)
* `coq` - compile all .v files
* `clean` - remove all files created by building
* `distclean` - remove all build artifacts, Clight, CoqMakefiles, coqdeps
