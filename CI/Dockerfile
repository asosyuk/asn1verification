FROM ubuntu:18.04
MAINTAINER p3rsik

# basic opam setup
RUN apt update && apt install -y software-properties-common && add-apt-repository ppa:avsm/ppa && apt update && \
    apt install -y build-essential m4 && apt install -y opam && \
    opam init --disable-sandboxing && eval $(opam env)

# create switches
RUN opam switch create vst 4.07.0 && \
    opam switch create clightgen 4.07.0

# clightgen installation
RUN opam switch clightgen && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev && \
    opam pin add coq 8.9.1 --yes && opam install menhir --yes
RUN eval $(opam env) && git clone https://github.com/AbsInt/CompCert.git && \
    cd CompCert && ./configure -clightgen x86_32-linux && make && cd ..

# vst installation
RUN opam switch vst && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev && \
    opam pin add coq 8.11.0 --yes && \
    opam install coq-struct-tact coq-ext-lib menhir --yes
RUN eval $(opam env) && git clone https://github.com/PrincetonUniversity/VST.git && \
    && cd VST && git checkout 1d31dd91774aee019aaa3d4e0a58ab8b0ccd63df && make && cd ..

RUN cp CompCert/compcert.ini /bin && cp CompCert/clightgen /bin && \
    cp /root/.opam/vst/bin/coqc /bin && cp /root/.opam/vst/bin/coq_makefile /bin

RUN apt update && apt install -y gcc-multilib lcov libasan*
