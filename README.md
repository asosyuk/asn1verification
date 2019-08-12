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
./configure.sh
make
```