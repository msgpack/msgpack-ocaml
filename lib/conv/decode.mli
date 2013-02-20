(** Dedocer util: extract specified value from Msgpack. otherwise raise error. *)
type t = Msgpack.Serialize.t

val int : t -> int
val int32 : t -> int32
val int64 : t -> int64
val map   : (t * t) list -> t
val str : t -> string
val array : t -> t list
val map   : t -> (t * t) list
