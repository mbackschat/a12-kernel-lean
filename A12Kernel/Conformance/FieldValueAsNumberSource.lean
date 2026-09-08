import A12Kernel.Elaboration.NumericSource

namespace A12Kernel.Conformance.FieldValueAsNumberSource

open A12Kernel

private def textSource : FlatFieldDecl :=
  { id := 0, groupPath := ["Root"], name := "Code"
    policy := { kind := .string }
    stringPatternSource := some "[0-9]+"
    stringPolicy := { maxLength := some 15 } }

private def enumSource (tokens : List String) : FlatFieldDecl :=
  { id := 1, groupPath := ["Root"], name := "Choice"
    policy := { kind := .enumeration }
    enumeration := some {
      storedTokens := ["A", "B"]
      categories := [{ name := "Numeric", tokens }] } }

private def diagnostic (source : FlatFieldDecl)
    (projection : EnumerationProjectionRef := .stored) : Option (Option String) :=
  match source.resolveFieldValueAsNumberSource projection with
  | .ok _ => none
  | .error error => some (error.diagnostic?.map (·.kernelCode))

example :
    diagnostic textSource = none ∧
    diagnostic { textSource with stringPatternSource := some "[0-9]*" } =
      some (some "MVK_NO_CONVERT_IN_NUMBER") ∧
    diagnostic { textSource with stringPolicy := { maxLength := some 16 } } =
      some (some "MVK_NO_CONVERT_IN_NUMBER") ∧
    diagnostic { textSource with stringPolicy := {} } =
      some (some "MVK_NO_CONVERT_IN_NUMBER") ∧
    diagnostic (enumSource [".5", "-1.25"]) (.category "Numeric") = none ∧
    diagnostic (enumSource [".5", "1."]) (.category "Numeric") =
      some (some "MVK_NO_CONVERT_IN_NUMBER") ∧
    diagnostic (enumSource ["1", "1234567890123456"]) (.category "Numeric") =
      some (some "MVK_NO_CONVERT_IN_NUMBER") := by
  native_decide

example :
    diagnostic textSource (.category "Numeric") = some none ∧
    diagnostic { textSource with customType := some { name := "Custom" } } =
      some none ∧
    diagnostic { textSource with stringValueMode := .raw } = some none ∧
    diagnostic { textSource with policy := { kind := .boolean } } = some none ∧
    diagnostic (enumSource [".5", "2"]) (.category "Missing") = some none ∧
    diagnostic (enumSource [".5"]) (.category "Numeric") = some none := by
  native_decide

end A12Kernel.Conformance.FieldValueAsNumberSource
