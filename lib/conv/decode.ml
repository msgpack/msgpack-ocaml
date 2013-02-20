open Base

type t = Msgpack.Serialize.t

let int = function
  | `PFixnum n | `Int8 n | `Int16 n
  | `NFixnum n | `Uint8 n   | `Uint16 n ->
    n
  | `Int32 n ->
    Int32.to_int n
  | `Int64 n | `Uint32 n ->
    Int64.to_int n
  | `Uint64 n ->
    Big_int.int_of_big_int n
  | _ ->
    errorf "Int expected"

let int32 = function
  | `PFixnum n | `Int8 n | `Int16 n
  | `NFixnum n | `Uint8 n   | `Uint16 n ->
    Int32.of_int n
  | `Int32 n ->
    n
  | `Int64 n | `Uint32 n ->
    Int64.to_int32 n
  | `Uint64 n ->
    Big_int.int32_of_big_int n
  | _ ->
    errorf "Int expected"

let int64  = function
  | `PFixnum n | `Int8 n | `Int16 n
  | `NFixnum n | `Uint8 n   | `Uint16 n ->
    Int64.of_int n
  | `Int32 n ->
    Int64.of_int32 n
  | `Int64 n | `Uint32 n ->
    n
  | `Uint64 n ->
    Big_int.int64_of_big_int n
  | _ ->
    errorf "Int expected"

let raw = function
  | `FixRaw xs | `Raw16 xs | `Raw32 xs ->
    xs
  | _ ->
    errorf "Raw expected"

let str t =
  ExtString.String.implode @@ raw t

let array = function
  | `FixArray xs | `Array16 xs | `Array32 xs ->
    xs
  | _ ->
    errorf "Array expected"

let map = function
  | `FixMap xs | `Map16 xs | `Map32 xs ->
    xs
  | _ ->
    errorf "Map expected"
