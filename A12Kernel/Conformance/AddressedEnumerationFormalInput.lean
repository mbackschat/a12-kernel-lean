import A12Kernel.Elaboration.AddressedEnumerationFormalInput

/-! # Addressed Enumeration formal-input locks -/

namespace A12Kernel.Conformance.AddressedEnumerationFormalInput

open A12Kernel

private def enumeration : EnumerationDeclaration := {
  storedTokens := ["A", "B"]
}

private def enumerationField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .enumeration }
  enumeration := some enumeration
}

private def target := enumerationField 1 "Target" ["Form", "Rows"] [10]
private def rootSource := enumerationField 2 "RootSource" ["Form"] []
private def unrelated := enumerationField 3 "Unrelated" ["Form"] []

private def model : FlatModel := {
  fields := [target, rootSource, unrelated]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 2 }
  ]
}

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def fieldOperation? :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] target.id
    (.field (.direct (parent rootSource.name)))).toOption

private def literalOperation? :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] target.id
    (.literal "A")).toOption

private def cell (field : FieldId) (path : List Nat) : ClassifiedCellInput := {
  address := { field, path }
  stored := "C"
  raw := .parsed (.enum "C")
}

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }
    ]
    cells := [cell rootSource.id [], cell target.id [1], cell unrelated.id []]
  }).toOption

/- Two runtime reads of one invalid root token retain one exact source finding, while the fieldless literal inventories none of the same document errors. -/
example :
    (do
      let fieldOperation ← fieldOperation?
      let literalOperation ← literalOperation?
      let input ← input?
      let fieldResult ←
        fieldOperation.executeResultWithFormalInputs input |>.toOption
      let literalResult ←
        literalOperation.executeResultWithFormalInputs input |>.toOption
      pure (fieldResult.string.formalErrorsInOperands,
        literalResult.string.formalErrorsInOperands)) = some ([{
          address := { field := rootSource.id, path := [] }
          cause := .declaredConstraint
        }], []) := by
  native_decide

end A12Kernel.Conformance.AddressedEnumerationFormalInput
