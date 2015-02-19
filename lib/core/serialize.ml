open Base

type t = Pack.t

let explode str =
  let res = ref [] in
  String.iter (fun c -> res := c :: !res) str;
  List.rev !res

let implode chars =
  let res = String.create (List.length chars) in
  List.iteri (fun i c -> res.[i] <- c) chars;
  res

let deserialize_string str =
  str
  +> explode
  +> List.map Pack.ascii8_of_char
  +> MsgpackCore.deserialize 0
  +> List.hd
  +> Pack.unpack

let serialize_string obj =
  obj
  +> Pack.pack
  +> MsgpackCore.serialize
  +> List.map Pack.char_of_ascii8
  +> implode
