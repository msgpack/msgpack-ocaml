let _ =
  OUnit.run_test_tt_main ("test" >::: [
    "pack.ml" >::: PackTest.tests;
    "serialize.ml" >::: SerializeTest.tests
  ])
