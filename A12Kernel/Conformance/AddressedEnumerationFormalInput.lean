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

private def defaultedEnumeration : EnumerationDeclaration := {
  enumeration with defaultStoredToken := some "B"
}

private def indexSource : FlatFieldDecl := {
  enumerationField 2 "Index" ["Form", "Rows"] [10] with
  enumeration := some defaultedEnumeration
}

private def model : FlatModel := {
  fields := [target, rootSource, unrelated]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 2 }
  ]
}

private def indexedModel : FlatModel := {
  fields := [target, indexSource, unrelated]
  repeatableGroups := [{
    level := 10
    path := ["Form", "Rows"]
    repeatability := some 2
    indexField := some indexSource.id
  }]
}

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def fieldOperation? :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] target.id
    (.field (.direct (parent rootSource.name)))).toOption

private def literalOperation? :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] target.id
    (.literal "A")).toOption

private def indexedOperation? :=
  (checkAddressedEnumerationComputation indexedModel ["Form", "Rows"] target.id
    (.field (.direct (bare indexSource.name)))).toOption

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

private def indexedPrepared : PreparedFlatStringContext indexedModel
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler indexedModel).toOption.get (by native_decide)

private def indexedCell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.enum stored)
}

private def indexedInput? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument indexedModel) :=
  (checkDocument indexedPrepared "en_US" { instantiatedRows := rows, cells }).toOption

private def indexedFinding (path : List Nat)
    (cause : FormalCause) : ComputationFormalInputFinding := {
  address := { field := indexSource.id, path }
  cause
}

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

/- A selected absent Enumeration index receives its full-call default before the addressed source read, so the result changes the source-filled target instead of clearing it. -/
example :
    (do
      let operation ← indexedOperation?
      let input ← indexedInput?
        [{ group := 10, path := [1] }]
        [indexedCell target.id [1] "A"]
      let result ← operation.executeResultWithFormalInputs input |>.toOption
      pure (result.string.withoutErrors.map fun item =>
          (item.targetField, item.value.text),
        result.string.withChanges.map fun item =>
          (item.targetField, item.value.text),
        result.string.cleared,
        result.string.formalErrorsInOperands)) =
      some ([({ field := target.id, path := [1] }, "B")],
        [({ field := target.id, path := [1] }, "B")], [], []) := by
  native_decide

/- Duplicate selected index values remain eager findings and poison the reached source reads, clearing both source-filled targets without becoming computed target errors. -/
example :
    (do
      let operation ← indexedOperation?
      let input ← indexedInput?
        [{ group := 10, path := [1] }, { group := 10, path := [2] }]
        [indexedCell indexSource.id [1] "A",
          indexedCell indexSource.id [2] "A",
          indexedCell target.id [1] "B",
          indexedCell target.id [2] "B"]
      let result ← operation.executeResultWithFormalInputs input |>.toOption
      let findings := result.string.formalErrorsInOperands
      pure (findings.length == 2 &&
          findings.contains (indexedFinding [1] .duplicateIndex) &&
          findings.contains (indexedFinding [2] .duplicateIndex),
        result.string.withoutErrors,
        result.string.withErrors,
        result.string.cleared)) =
      some (true, [], [], [
        { field := target.id, path := [1] },
        { field := target.id, path := [2] }
      ]) := by
  native_decide

end A12Kernel.Conformance.AddressedEnumerationFormalInput
