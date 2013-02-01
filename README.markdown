MsgPack for OCaml
==============================

BULID
------------

    $ make
    $ sudo make install

EXAMPLE
------------

TBD

TEST
------------

    $ ocaml setup.ml -configure --enable-tests
    $ make test

PROOF
-----------

If you want to use msgpack at OCaml, you need not do this section.
This section for user intrested in formal verification.

You need Coq 8.4 and omake.

    $ cd proof
    $ make
    $ cp *.ml ../lib

