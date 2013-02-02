(** MessagePack for OCaml *)

(** MessagePack Serializer *)
module Serialize : sig
  (** MesagePack object. See also {{:http://redmine.msgpack.org/projects/msgpack/wiki/FormatSpec}MessagePack specification}. *)
  type t =
      [ `Bool of bool
      | `Nil
      | `PFixnum of int
      | `NFixnum of int
      | `Uint8 of int
      | `Uint16 of int
      | `Uint32 of int64
      | `Uint64 of Big_int.big_int
      | `Int8 of int
      | `Int16 of int
      | `Int32 of int32
      | `Int64 of int64
      | `Float of float
      | `Double of float
      | `FixRaw of char list
      | `Raw16 of char list
      | `Raw32 of char list
      | `FixArray of t list
      | `Array16 of t list
      | `Array32 of t list
      | `FixMap of (t * t) list
      | `Map16 of (t * t) list
      | `Map32 of (t * t) list ]

  (**  [MessagePack.Serialize.deserialize_string str] deserialize MessagePack string [str] to MessagePack object. *)
  val deserialize_string : string -> t

  (**  [MessagePack.Serialize.serialize_string obj] serialize MessagePack object [obj] to MessagePack string. *)
  val serialize_string   : t -> string
end

module Config : sig
  val version : int * int * int
end

module MsgpackCore : sig
  type ascii =
    | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

  type ascii8 = ascii
  type ascii16 = ascii8 * ascii8
  type ascii32 = ascii16 * ascii16
  type ascii64 = ascii32 * ascii32

  type object0 =
    | Bool of bool
    | Nil
    | PFixnum of ascii8
    | NFixnum of ascii8
    | Uint8 of ascii8
    | Uint16 of ascii16
    | Uint32 of ascii32
    | Uint64 of ascii64
    | Int8 of ascii8
    | Int16 of ascii16
    | Int32 of ascii32
    | Int64 of ascii64
    | Float of ascii32
    | Double of ascii64
    | FixRaw of ascii8 list
    | Raw16 of ascii8 list
    | Raw32 of ascii8 list
    | FixArray of object0 list
    | Array16 of object0 list
    | Array32 of object0 list
    | FixMap of (object0 * object0) list
    | Map16 of (object0 * object0) list
    | Map32 of (object0 * object0) list
end

(** Conversion MessagePack object between OCaml and Coq. *)
module Pack : sig
  (** exception when MesagePack object is invalid form *)
  exception Not_conversion of string
  val pack : Serialize.t -> MsgpackCore.object0
  val unpack : MsgpackCore.object0 -> Serialize.t
end
