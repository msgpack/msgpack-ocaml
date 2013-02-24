#!/bin/sh
ocamlfind ocamlc -linkpkg -package msgpack -package msgpack.conv -package meta_conv.syntax -syntax camlp4o example.ml
