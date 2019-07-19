## `clightgen`
### Installation

`clightgen` can be installed as part of CompCert via OPAM:
```
opam repo add coq-released http://coq.inria.fr/opam/released
opam install coq-compcert
```

### Usage

File `BOOLEAN.v` contains the output of clightgen on `asn1c/skeletons/BOOLEAN.c`.

Options `-fstruct-passing -flongdouble` are required due to the features unsupported by CompCert:
functions returning a struct/union and long double.

```bash
clightgen -normalize -fstruct-passing -flongdouble `# generator options`    \
          -I asn1c/skeletons                       `# include dependencies` \
          asn1c/skeletons/BOOLEAN.c                `# input file`           \
          -o BOOLEAN.v                             `# output file`
```

Some useful options of `clightgen`:
```
   -I <dir>     search <dir> for include files
   -D <symbol>  define preprocessor macro
   -U <symbol>  undefine preprocessor macro
   -dclight     create readable C light code
```
