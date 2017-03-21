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
  +> List.rev_map Pack.ascii8_of_char
  +> List.rev
  +> MsgpackCore.deserialize 0
  +> List.hd
  +> Pack.unpack

let serialize_string obj =
  obj
  +> Pack.pack
  +> (fun objs -> MsgpackCore.serialize_rev objs [])
  +> List.rev_map Pack.char_of_ascii8
  +> implode
