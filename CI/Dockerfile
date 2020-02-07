FROM ubuntu:18.04
MAINTAINER p3rsik

# basic opam setup
RUN apt update && apt install -y software-properties-common && add-apt-repository ppa:avsm/ppa && apt update && \
    apt install -y build-essential && apt install -y opam && \
    opam init --disable-sandboxing && eval $(opam env) &&

# create switches
RUN opam switch create vst 4.07.0 && \
    opam switch create clightgen 4.07.0

# clightgen installation
RUN opam switch clightgen && eval $(opam env) && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \ 
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev && \ 
    opam pin coq 8.9.0 && \ 
    git clone https://github.com/AbsInt/CompCert.git && \ 
    cd compcert && ./configure -clightgen x86_32-linux && make -j && cd ..

# vst installation
RUN opam switch vst && eval $(opam env) && \ 
    opam repo add coq-released https://coq.inria.fr/opam/released && \ 
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev && \
    opam pin coq 8.10.1 && \
    opam -y install coq-struct-tact && \
    git clone https://github.com/PrincetonUniversity/VST.git && \
    cd VST && make -j && cd .. && \
    git clone https://p3rsik@bitbucket.org/codeminders/asn1verification.git

# copying clightgen to src folder for make to use
RUN cp compcert/clightgen asn1verification/src/ && cd asn1verification/src
