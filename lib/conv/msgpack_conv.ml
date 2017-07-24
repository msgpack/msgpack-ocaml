open MsgpackBase

include Meta_conv.Coder.Make(struct

  type target = Msgpack.Serialize.t

  let format _ =
    assert false

  module Constr = struct
    let tuple =
      Encode.array

    let variant _ tag = function
      | [] -> Encode.str tag
      | ts -> Encode.map [Encode.str tag, Encode.array ts]

    let poly_variant =
      variant

    let record _ ts =
      Encode.map @@ List.map (fun (key, value) ->
        (Encode.str key, value)) ts

    let object_ =
      record
  end

  module Deconstr = struct
    let tuple =
      Decode.array

    let variant _ = function
      | `FixRaw tag | `Raw16 tag | `Raw32 tag ->
        implode tag, []
      | `FixMap [tag, ts] | `Map16 [tag, ts] | `Map32 [tag, ts] ->
        Decode.str tag, Decode.array ts
      | _ ->
        errorf "Object expected for variant"

    let poly_variant =
      variant

    let record _ t =
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
