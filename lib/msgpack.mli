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

module Open : sig
  module Msgpack : sig
    type t = Serialize.t
  end

  module Msgpack_conv : sig
    open Meta_conv.Types
    open Meta_conv.Open

    include Meta_conv.Types.S with type target = Msgpack.t

    val msgpack_of_int       : int encoder
    val msgpack_of_nativeint : nativeint encoder
    val msgpack_of_unit      : unit encoder
    val msgpack_of_bool      : bool encoder
    val msgpack_of_int32     : int32 encoder
    val msgpack_of_int64     : int64 encoder
    val msgpack_of_float     : float encoder
    val msgpack_of_char      : char encoder
    val msgpack_of_string    : string encoder
    val msgpack_of_list      : 'a encoder -> 'a list encoder
    val msgpack_of_array     : 'a encoder -> 'a array encoder
    val msgpack_of_option    : 'a encoder -> 'a option encoder
    val msgpack_of_lazy_t    : 'a encoder -> 'a Lazy.t encoder

    val int_of_msgpack       : int decoder
    val nativeint_of_msgpack : nativeint decoder
    val unit_of_msgpack      : unit decoder
    val bool_of_msgpack      : bool decoder
    val int32_of_msgpack     : int32 decoder
    val int64_of_msgpack     : int64 decoder
    val float_of_msgpack     : float decoder
    val char_of_msgpack      : char decoder
    val string_of_msgpack    : string decoder
    val list_of_msgpack      : 'a decoder -> 'a list decoder
    val array_of_msgpack     : 'a decoder -> 'a array decoder
    val option_of_msgpack    : 'a decoder -> 'a option decoder
    val lazy_t_of_msgpack    : 'a decoder -> 'a lazy_t decoder
  end
end
