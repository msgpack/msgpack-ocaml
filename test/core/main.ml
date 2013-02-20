
let _ =
  OUnit.(run_test_tt_main ("core" >::: [
    "pack.ml" >::: PackTest.tests;
    "serialize.ml" >::: SerializeTest.tests;
  ]))
