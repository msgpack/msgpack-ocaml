open MsgpackBase

type t = Pack.t

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
