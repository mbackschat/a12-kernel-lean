import A12Kernel.Elaboration.Flat

/-! # Direct String and Length conformance locks -/

namespace A12Kernel.Conformance.StringLength

open A12Kernel

private def stringField : FlatStringField := { id := 6 }

private def checked (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .string } raw

private def context (raw : RawCell) : FlatContext where
  read _ := checked raw

private def noncanonicalPresentEmptyContext : FlatContext where
  read _ := { rawPresent := true, parsed := some (.str ""), findings := [] }

private def directEqualsAbc : FlatCondition :=
  .compare (.string .equal stringField "ABC")

private def directEqualsEmpty : FlatCondition :=
  .compare (.string .equal stringField "")

private def directNotEqualsAbc : FlatCondition :=
  .compare (.string .notEqual stringField "ABC")

private def directNotEqualsEmpty : FlatCondition :=
  .compare (.string .notEqual stringField "")

private def lengthLessThanFive : FlatCondition :=
  .compare (.stringLength .less stringField 5)

private def lengthGreaterOrEqualZero : FlatCondition :=
  .compare (.stringLength .greaterEqual stringField 0)

example : directEqualsAbc.evalFull (context .empty) true = .notFired := by
  decide

example : lengthLessThanFive.evalFull (context .empty) true = .fired .omission := by
  native_decide

example : lengthGreaterOrEqualZero.evalFull (context .empty) true = .fired .value := by
  native_decide

example : directEqualsAbc.evalFull (context (.parsed (.str ""))) true = .notFired := by
  decide

example : lengthLessThanFive.evalFull (context (.parsed (.str ""))) true = .fired .omission := by
  native_decide

example : lengthLessThanFive.evalFull noncanonicalPresentEmptyContext true = .fired .omission := by
  native_decide

example : directEqualsAbc.evalFull (context .empty) false = .notFired := by
  decide

example : lengthLessThanFive.evalFull (context .empty) false = .notFired := by
  decide

example : lengthGreaterOrEqualZero.evalFull (context .empty) false = .notFired := by
  decide

example : directEqualsAbc.evalFull (context (.parsed (.str "ABC"))) true = .fired .value := by
  decide

example : lengthLessThanFive.evalFull (context (.parsed (.str "ABC"))) true = .fired .value := by
  native_decide

example : lengthGreaterOrEqualZero.evalFull (context (.parsed (.str "ABC"))) true =
    .fired .value := by
  native_decide

example : directEqualsAbc.evalFull (context (.parsed (.str "ABCDEF"))) true = .notFired := by
  decide

example : lengthLessThanFive.evalFull (context (.parsed (.str "ABCDEF"))) true = .notFired := by
  native_decide

example : lengthGreaterOrEqualZero.evalFull (context (.parsed (.str "ABCDEF"))) true =
    .fired .value := by
  native_decide

example : directEqualsEmpty.evalFull (context (.parsed (.str "ABC"))) true = .notFired := by
  decide

example : directNotEqualsAbc.evalFull (context .empty) true = .notFired := by
  decide

example : directNotEqualsAbc.evalFull (context (.parsed (.str "ABC"))) true = .notFired := by
  decide

example : directNotEqualsAbc.evalFull (context (.parsed (.str "XYZ"))) true =
    .fired .value := by
  decide

example : directNotEqualsEmpty.evalFull (context (.parsed (.str "ABC"))) true =
    .notFired := by
  decide

example : directNotEqualsEmpty.evalFull (context (.rejected .malformed)) true =
    .unknown := by
  decide

example : directEqualsEmpty.evalFull (context (.rejected .malformed)) true = .unknown := by
  decide

example : directEqualsEmpty.evalFull (context (.parsed (.num 1))) true = .unknown := by
  decide

example : directEqualsAbc.evalFull (context (.rejected .malformed)) true = .unknown := by
  decide

example : lengthLessThanFive.evalFull (context (.rejected .malformed)) true = .unknown := by
  decide

example : directEqualsAbc.evalFull (context (.parsed (.num 1))) true = .unknown := by
  decide

example : lengthLessThanFive.evalFull (context (.parsed (.num 1))) true = .unknown := by
  decide

/- Field kind alone does not determine empty behavior: the same observation is suppressed by direct equality and fires through Length. -/
example : directEqualsAbc.evalFull (context .empty) true !=
    lengthLessThanFive.evalFull (context .empty) true := by
  native_decide

/- A substituted empty result is not uniformly omission-typed: direction makes `Length >= 0` a value firing. -/
example : lengthLessThanFive.evalFull (context .empty) true !=
    lengthGreaterOrEqualZero.evalFull (context .empty) true := by
  native_decide

example : utf16CodeUnitLength "é" = 2 := by
  native_decide

example : utf16CodeUnitLength "😀" = 2 := by
  native_decide

private def productCodePath : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := "ProductCode" }

private def productCodeDecl : FlatFieldDecl :=
  { id := stringField.id, groupPath := ["Order"], name := "ProductCode",
    policy := { kind := .string } }

private def productCodeModel : FlatModel :=
  { fields := [productCodeDecl] }

private def quantityDecl : FlatFieldDecl :=
  { id := 7, groupPath := ["Order"], name := "Quantity",
    policy := { kind := .number { scale := 0, signed := false } } }

private def numberModel : FlatModel :=
  { fields := [quantityDecl] }

private def quantityPath : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := "Quantity" }

private def elaborationError? : Except ElabError α → Option ElabError
  | .ok _ => none
  | .error error => some error

example : (elaborate productCodeModel ["Order"]
    (.compare .equal productCodePath (.string "ABC"))).isOk = true := by
  native_decide

example : (elaborate productCodeModel ["Order"]
    (.lengthCompare .less productCodePath 5)).isOk = true := by
  native_decide

example : (elaborate productCodeModel ["Order"]
    (.lengthCompare .greaterEqual productCodePath 0)).isOk = true := by
  native_decide

example : (elaborate productCodeModel ["Order"]
    (.compare .notEqual productCodePath (.string "ABC"))).isOk = true := by
  native_decide

example : elaborationError? (elaborate productCodeModel ["Order"]
    (.lengthCompare .greater productCodePath 0)) =
    some (.unsupportedOperator .greater) := by
  native_decide

example : elaborationError? (elaborate numberModel ["Order"]
    (.lengthCompare .less quantityPath 5)) =
    some (.lengthOperandKindMismatch ["Order", "Quantity"] .number) := by
  native_decide

example : (elaborate productCodeModel ["Order"]
    (.fieldNotFilled productCodePath)).isOk = true := by
  native_decide

end A12Kernel.Conformance.StringLength
