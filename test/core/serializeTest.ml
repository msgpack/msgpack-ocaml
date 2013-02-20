open OUnit
open Msgpack.Serialize

let tests = [
  "Rubyのライブラリとの互換テスト(deserialize)" >:: begin fun _ ->
    (* [1,2,3].to_msgpack *)
    assert_equal (`FixArray [`PFixnum 1; `PFixnum 2; `PFixnum 3])
      (deserialize_string "\147\001\002\003")
  end;
  "Rubyのライブラリとの互換テスト(serialize)" >:: begin fun _ ->
    assert_equal "\147\001\002\003"
      (serialize_string (`FixArray [`PFixnum 1; `PFixnum 2; `PFixnum 3]))
  end
]
