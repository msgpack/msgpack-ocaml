(* serialize *)
let bytes =
  Msgpack.Serialize.serialize_string ((`FixArray [`PFixnum 1; `PFixnum 2; `PFixnum 3]) : Msgpack.Serialize.t)

(* deserialize *)
let obj =
  Msgpack.Serialize.deserialize_string bytes

open Msgpack_conv

type t = {
  int : int;
  str : string;
} [@@deriving conv{msgpack}]

(* serialize *)
let bytes =
  Msgpack.Serialize.serialize_string (msgpack_of_t { int = 42; str = "ans" })

(* deserialize *)
let obj =
  t_of_msgpack (Msgpack.Serialize.deserialize_string bytes)


