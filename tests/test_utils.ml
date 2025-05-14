let test_transform_Aarrow_to_Uarrow() =
  let expected = "a → b" in
  let actual = Common.Util.transform_ascii_to_unicode "a -> b" in
  Alcotest.(check string) "Aarrow to Uarrow" expected actual
  let test_transform_Forall_to_Pi_withSpaces() =
  let expected = " Π x, y" in
  let actual = Common.Util.transform_ascii_to_unicode " forall x, y" in
  Alcotest.(check string) "Forall to Pi withSpaces" expected actual
  let test_transform_Forall_to_Pi_at_begining() =
  let expected = "Π x, y" in
  let actual = Common.Util.transform_ascii_to_unicode "forall x, y" in
  Alcotest.(check string) "Forall to Pi at begining" expected actual
  let test_transform_Forall_to_Pi_with_dot() =
  let expected = "Π.x, y" in
  let actual = Common.Util.transform_ascii_to_unicode "forall.x, y" in
  Alcotest.(check string) "Forall to Pi with dot" expected actual
  let test_transform_Forall_to_Pi_with_parathensis() =
  let expected = "((Π x, y" in
  let actual = Common.Util.transform_ascii_to_unicode "((forall x, y" in
  Alcotest.(check string) "Forall to Pi with parathensis" expected actual

let () =
  let open Alcotest in
  run "Test_tests" [
    ("TransformArrow", [ test_case "Arrow" `Quick test_transform_Aarrow_to_Uarrow
                       ; test_case "forall with spaces" `Quick test_transform_Forall_to_Pi_withSpaces
                       ; test_case "forall at begining" `Quick test_transform_Forall_to_Pi_at_begining
                       ; test_case "forall with with a dot" `Quick test_transform_Forall_to_Pi_with_dot
                       ; test_case "forall with parathensis" `Quick test_transform_Forall_to_Pi_with_parathensis
    ])

  ]