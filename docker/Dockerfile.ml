FROM ocaml/opam:debian-7_ocaml-4.04.0

RUN opam update && \
      opam install -y oasis ounit ppx_meta_conv ocamlfind && \
      rm -rf /home/opam/opam-repository

WORKDIR /msgpack-ocaml
