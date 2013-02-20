(** provide meta_conv types *)
open Meta_conv.Types
open Meta_conv.Open

include Meta_conv.Types.S with type target = Msgpack.Serialize.t

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
