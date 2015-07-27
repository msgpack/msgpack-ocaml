MsgPack for OCaml
==============================

BULID
------------

``` bash
$ make
$ sudo make install
```

EXAMPLE
------------

### Serialize/Deserialize for Msgpack Object

``` ocaml
(* serialize *)
let bytes = 
  Msgpack.Serialize.serialize_string (`FixArray [`PFixnum 1; `PFixnum 2; `PFixnum 3])

(* deserialize *)
let obj =
  Msgpack.Serialize.deserialize_string bytes
```

### Serialize/Deserialize for OCaml types (with meta_conv)

``` ocaml
open Msgpack_conv

type t = {
  int : int;
  str : string;
} with conv(msgpack)

(* serialize *)
let bytes = 
  Msgpack.Serialize.serialize_string (msgpack_of_t { int = 42; str = "ans" })

(* deserialize *)
let obj =
  t_of_msgpack (Msgpack.Serialize.deserialize_string bytes)
```

See also, `examlpe/`

TEST
------------

``` bash
$ ocaml setup.ml -configure --enable-tests
$ make test
```

PROOF
-----------

If you want to use msgpack at OCaml, you need not do this section.
This section for user intrested in formal verification.

You need Coq 8.4 and omake.

``` bash
$ cd proof
$ make
$ cp *.ml ../lib
```

