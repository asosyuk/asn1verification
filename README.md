# asn1verification
Verification of the [asn1c](https://github.com/vlm/asn1c) compiler in Coq using compcert

# asn1verification using vst

## Dependencies
``` shell
opam repo add coq-released http://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

opam pin add coq 8.10.1
opam install coq-struct-tact coq-ext-lib
```
Clone asn1c project in the directory of your choice:

``` shell
git clone git@bitbucket.org:codeminders/asn1c.git
git checkout vst_modifications
```

Download and install VST 2.5 in the same directory
https://github.com/PrincetonUniversity/VST/releases/tag/v2.5
Follow instructions in VST.README and VST.BUILD_ORGANIZATION to install VST

Install CompCert
``` opam install coq-compcert3.5+8.10
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
