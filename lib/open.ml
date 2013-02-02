open Base

module Msgpack = struct
  type t = Pack.t
end

let errorf fmt =
  Printf.ksprintf (fun s -> failwith (Printf.sprintf "Msgpack_conv: %s" s)) fmt

module Encode = struct
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
    raw @@ ExtString.String.explode s

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
end

module Decode = struct
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

  let raw = function
    | `FixRaw xs | `Raw16 xs | `Raw32 xs ->
      xs
    | _ ->
      errorf "Raw expected"

  let str t =
    ExtString.String.implode @@ raw t

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



end

module Msgpack_conv = struct
  include Meta_conv.Coder.Make(struct

    type target = Msgpack.t

    let format _ =
      assert false

    module Constr = struct
      let tuple =
        Encode.array

      let variant tag = function
        | [] -> Encode.str tag
        | ts -> Encode.map [Encode.str tag, Encode.array ts]

      let poly_variant =
        variant

      let record ts =
        Encode.map @@ List.map (fun (key, value) ->
          (Encode.str key, value)) ts

      let object_ =
        record
    end

    module Deconstr = struct
      let tuple =
        Decode.array

      let variant = function
        | `FixRaw tag | `Raw16 tag | `Raw32 tag ->
          ExtString.String.implode tag, []
        | `FixMap [tag, ts] | `Map16 [tag, ts] | `Map32 [tag, ts] ->
          Decode.str tag, Decode.array ts
        | _ ->
          errorf "Object expected for variant"

      let poly_variant =
        variant

      let record t =
        Decode.map t
        +> List.map (fun (key, value) ->
          (Decode.str key, value))

      let object_  =
        record
    end

  end)

  let msgpack_of_int =
    Encode.int

  let msgpack_of_unit () =
    `Nil

  let msgpack_of_bool b =
    `Bool b

  let msgpack_of_nativeint n =
    if Sys.word_size = 32 then
      `Int32 (Nativeint.to_int32 n)
    else
      `Int64 (Int64.of_nativeint n)

  let msgpack_of_int32 n =
    `Int32 n

  let msgpack_of_int64 n =
    `Int64 n

  let msgpack_of_float d =
    if Int32.to_float (Int32.of_float d) = d then
      (* float *)
      `Float d
    else
      `Double d

  let msgpack_of_char c =
    `FixRaw [ c ]

  let msgpack_of_string =
    Encode.str

  let msgpack_of_list f xs =
    Encode.array @@ List.map f xs

  let msgpack_of_array f xs =
    Encode.array @@ List.map f @@ Array.to_list xs

  let msgpack_of_option f = function
    | None ->
        `Nil
    | Some v ->
        f v

  let msgpack_of_lazy_t f x =
    f (Lazy.force x)

  let int_of_msgpack =
    Helper.of_deconstr Decode.int

  let nativeint_of_msgpack =
    Helper.of_deconstr (fun n ->
      Int64.to_nativeint @@ Decode.int64 n)

  let int32_of_msgpack =
    Helper.of_deconstr Decode.int32

  let int64_of_msgpack =
    Helper.of_deconstr Decode.int64

  let unit_of_msgpack =
    Helper.of_deconstr (function
      | `Nil -> ()
      | _ -> errorf "nil expected")

  let bool_of_msgpack =
    Helper.of_deconstr (function
      | `Bool b  -> b
      | _ -> errorf "bool expected")

  let float_of_msgpack =
    Helper.of_deconstr (function
      | `Float d | `Double d -> d
      | _ -> errorf "float expected")

  let char_of_msgpack =
    Helper.of_deconstr (function
      | `FixRaw [ c ] -> c
      | _ -> errorf "char expected")

  let string_of_msgpack    : string decoder =
    Helper.of_deconstr Decode.str

  let list_of_msgpack f =
    Helper.list_of (function
      | `FixArray xs | `Array16 xs | `Array32 xs ->
          Some xs
      | _ ->
          None) f

  let array_of_msgpack f =
    Helper.array_of (function
      | `FixArray xs | `Array16 xs | `Array32 xs ->
          Some xs
      | _ ->
          None) f

  let option_of_msgpack f =
    Helper.option_of (function
      | `Nil -> Some None
      | v    -> Some (Some v))
      f

  let lazy_t_of_msgpack    f : 'a lazy_t decoder =
    Helper.lazy_t_of (fun e -> raise (Error e)) f

end
