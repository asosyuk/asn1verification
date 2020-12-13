FROM ubuntu:18.04
MAINTAINER p3rsik

# basic opam setup
RUN apt update && apt install -y software-properties-common && add-apt-repository ppa:avsm/ppa && apt update && \
    apt install -y build-essential m4 && apt install -y opam && \
    opam init --disable-sandboxing && eval $(opam env)

# clightgen installation
RUN opam pin add coq 8.11.0 --yes && opam install menhir --yes && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev && \
    opam install coq-compcert.3.7 --yes

# vst installation
RUN opam install coq-struct-tact coq-ext-lib --yes
RUN opam install coq-vst.2.6 --yes

RUN apt update && apt install -y gcc-multilib lcov libasan*
