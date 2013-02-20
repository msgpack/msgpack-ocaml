(** Encode util: encode value to msgpack object *)
type t = Msgpack.Serialize.t

val int : int -> t
val str : string -> t
val array : t list -> t
val map   : (t * t) list -> t
