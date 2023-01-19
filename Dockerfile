FROM ubuntu:jammy

ARG DEBIAN_FRONTEND=noninteractive
# Install some basic pre-requisites
RUN apt-get -qq update \
  && apt-get install -q -y \
    sudo wget git \
    build-essential g++ gcc m4 make pkg-config libgmp3-dev unzip cmake \
    opam \
    python3 python3-pip \
    time \
    z3 \
    libz3-dev \
  && apt-get clean -q -y \
  && rm -rf /var/lib/apt/lists/*

RUN pip3 install solc-select
RUN solc-select install 0.7.6 \
  && solc-select use 0.7.6 \
  && solc-select install 0.4.26
ENV PATH=$PATH:/root/.solc-select/artifacts/

WORKDIR /build
ADD . ./verismart

WORKDIR /build/verismart
RUN opam init -y --disable-sandboxing \
  && eval $(opam env) \
  && opam update \
  && opam install -y \
    conf-m4.1 ocamlfind ocamlbuild num yojson batteries ocamlgraph zarith z3
# Make sure that ocamlbuild and such exists in the path
RUN echo 'eval $(opam env)' >> $HOME/.bashrc

RUN chmod +x build && eval $(opam env) && ./build && ./main.native --help >/dev/null
RUN ln -s $(realpath ./main.native) /usr/local/bin/verismart
