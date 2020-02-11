# asn1verification
Verification of the [asn1c](https://github.com/vlm/asn1c) compiler in Coq using compcert

# asn1verification with compcert

## Dependencies
``` shell
opam repo add coq-released http://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

opam pin add coq 8.8.2
opam install coq-compcert coq-struct-tact
```

## Building compcert
``` shell
cd src
make clight coq
```

# asn1verification using vst

## Dependencies
``` shell
opam repo add coq-released http://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

opam pin add coq 8.10.1
opam install coq-struct-tact coq-ext-lib
```
Clone VST in the directory of your choice and compile it:
``` shell
git clone  git@github.com:PrincetonUniversity/VST.git
or
git clone https://github.com/PrincetonUniversity/VST.git
```
and then
```shell
cd VST
make -j
```

Create new opam switch to compile compcert clightgen and compile it:
```shell
opam switch create clightgen 4.07.0
git clone git@github.com:AbsInt/CompCert.git
or
git clone https://github.com/AbsInt/CompCert.git
```
and then
```shell
cd compcert
./configure -clightgen x86_32-linux
make
cp clightgen [asn1verification_directory]/src
```
Don't forget to switch back to your default switch

## Building asn1verification project
``` shell
cd src
make clight coq
```

## `make` targets
* `clight` - generate Clight files from C sources (generated .v files are not compiled)
* `coq` - compile all .v files
* `clean` - remove all files created by building
* `distclean` - remove all build artifacts, Clight, CoqMakefiles, coqdeps
