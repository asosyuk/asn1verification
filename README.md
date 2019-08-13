# asn1verificatoin
Verification of the [asn1c](https://github.com/vlm/asn1c) compiler in Coq

## Dependencies
``` shell
opam repo add coq-released http://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

opam pin add coq 8.8.2
opam install coq-compcert coq-struct-tact
```

## Building
``` shell
cd src
make clight coq
```

## `make` targets
* `clight` - generate Clight files from C sources (generated .v files are not compiled)
* `coq` - compile all .v files
* `clean` - remove all files created by building
* `distclean` - remove all build artifacts, Clight, CoqMakefiles, coqdeps