FROM ocaml/opam:debian-7_ocaml-4.04.0

USER root

RUN apt-get update && \
      apt-get install libgmp-dev -y --no-install-recommends && \
apt-get clean && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

USER opam

RUN opam update && \
      opam install -y oasis ounit ppx_meta_conv ocamlfind opam-publish && \
      rm -rf /home/opam/opam-repository

WORKDIR /msgpack-ocaml
