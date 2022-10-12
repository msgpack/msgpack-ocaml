#!/bin/sh
ocamlfind ocamlc -linkpkg -package msgpack -package msgpack-conv -package ppx_meta_conv.ppx example.ml
