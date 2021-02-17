FROM ubuntu:18.04

# basic opam setup
RUN apt update && apt install -y software-properties-common && add-apt-repository ppa:avsm/ppa && apt update && \
    apt install -y build-essential m4 && apt install -y opam && \
    opam init --disable-sandboxing && eval $(opam env)

# clightgen installation
RUN opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam update && \
    opam pin add coq 8.12.2 --yes && opam install menhir --yes && \
    opam install coq-compcert.3.7+8.12~coq_platform  --yes

# vst installation
RUN opam pin add coq-struct-tact https://github.com/uwplse/StructTact.git -k git --yes && \
    opam install coq-ext-lib --yes && \
    opam install coq-vst.2.6 --yes && \
    eval $(opam env)

RUN apt update && apt install -y gcc-multilib lcov libasan*
