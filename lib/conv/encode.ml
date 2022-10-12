open Msgpack__MsgpackBase

type t = Msgpack.Serialize.t

let int n =
  if 0 <= n then begin
    (* positive *)
    if n <= 127 then
      `PFixnum n
    else if n <= 0xFF then
      `Uint8 n
    else if n <= 0xFFFF then
      `Uint16 n
    else if (Int64.of_int n) <= 0xFFFF_FFFFL then
      `Uint32 (Int64.of_int n)
    else
      `Uint64 (Big_int.big_int_of_int n)
  end else begin
    (* negative *)
    if -32 <= n then
      `NFixnum n
    else if -127 <= n then
      `Int8 n
    else if -32767 <= n then
      `Int16 n
    else if -2147483647l <= (Int32.of_int n) then
      `Int32 (Int32.of_int n)
    else
      `Int64 (Int64.of_int n)
  end

let raw xs =
  let n =
    List.length xs
  in
  if n < 32 then
    `FixRaw xs
  else if n <= 0xFFFF then
    `Raw16 xs
  else
    `Raw32 xs

let str s =
  raw @@ explode s

let array xs =
  let n =
    List.length xs
  in
  if n < 15 then
    `FixArray xs
  else if n <= 0xFFFF then
    `Array16 xs
  else
    `Array32 xs

let map xs =
  let n =
    List.length xs
  in
  if n < 32 then
    `FixMap xs
  else if n <= 0xFFFF then
    `Map16 xs
  else
    `Map32 xs

