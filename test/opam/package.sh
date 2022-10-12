#!/bin/bash

git clean -fdx
cd $PWD/$(git rev-parse --show-cdup)
opam pin add . -y

cd examples
./build.sh
./a.out && echo "ok"
