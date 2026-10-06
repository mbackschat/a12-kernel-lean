import A12Kernel.Elaboration.ValidationCondition.Assembly

namespace A12Kernel.Conformance.ValueListCondition

open A12Kernel

private def model : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Form"], name := "Text", policy := { kind := .string } },
      { id := 2, groupPath := ["Form"], name := "N", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 3, groupPath := ["Form"], name := "M", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 4, groupPath := ["Form", "Rows"], name := "T", repeatableScope := [10], policy := { kind := .string } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def direct (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field := name }
private def star : SurfaceFieldEntityOperand :=
  .star { base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "T" }
private def sides : List (CheckedValueListCondition model) :=
  [(elaborateNumberEntityValueListSource model ["Form"]
      { quantifier := .atLeastOne, fields := { first := direct "N", rest := [] }
        values := { first := direct "M", rest := [] } }).toOption.map .number,
   (elaborateTokenEntityValueListSource model ["Form"]
      { quantifier := .atLeastOne, fields := { first := star, rest := [] }
        values := { first := direct "Text", rest := [] } }).toOption.map .token,
   (elaborateTokenEntityStringLiteralValueListSource model ["Form"]
      { quantifier := .atLeastOne, fields := { first := star, rest := [] }
        values := ["x"] }).toOption.map .literals].filterMap id

private def document? : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := [
      { address := { field := 1, path := [] }, stored := "x", raw := .parsed (.str "x") },
      { address := { field := 2, path := [] }, stored := "1", raw := .parsed (.num 1) },
      { address := { field := 3, path := [] }, stored := "1", raw := .parsed (.num 1) },
      { address := { field := 4, path := [1] }, stored := "x", raw := .parsed (.str "x") }] }).toOption

private def outcomes : Option (List (Option Verdict × Option Verdict × Option Verdict)) := do
  let document ← document?
  let context : AddressedValidationEvaluationContext model :=
    { scalar := { fields := document.flatContext, groups := .unavailable }
      outer := [], input := .checked document }
  let legacy := { context with input := .legacy document.source.toDocument fun _ => document.flatContext.read }
  sides.mapM fun source => do
    let checked ← (CheckedValidationCondition.fromValueList ["Form"] source).toOption
    let present : ValidationCondition model := .leaf (.flat (.fieldFilled (.string { id := 1 })))
    let absent : ValidationCondition model := .leaf (.flat (.fieldNotFilled (.string { id := 1 })))
    pure ((checked.core.evalAddressed context).toOption,
      (ValidationCondition.evalAddressed (.or present checked.core) legacy).toOption,
      (ValidationCondition.evalAddressed (.and absent checked.core) legacy).toOption)

example : sides.length = 3 ∧ outcomes = some (List.replicate 3
    (some (.fired .value), some (.fired .value), some .notFired)) := by
  native_decide

private def unsupportedInputs : Option (List (Bool × Bool)) := do
  let document ← document?
  let context : AddressedValidationEvaluationContext model :=
    { scalar := { fields := document.flatContext, groups := .unavailable }
      outer := [], input := .legacy document.source.toDocument fun _ => document.flatContext.read }
  let partialContext := { context with input := .partialView document fun _ _ => pure none }
  let refuses : Except CheckedAddressingError Verdict → Bool
    | .error (.checkedDocumentRequired []) => true
    | _ => false
  pure (sides.map fun source =>
    let leaf := ValidationConditionLeaf.valueList source
    (refuses (leaf.evalAddressed context), refuses (leaf.evalAddressed partialContext)))

example : unsupportedInputs = some (List.replicate 3 (true, true)) := by
  native_decide

example :
    (sides.map fun source =>
      ((ValidationConditionLeaf.valueList source).requiresAddressedValidation,
       (ValidationConditionLeaf.valueList source).supportsAddressedPartial,
       source.bindingScopes.flatten.isEmpty)) = List.replicate 3 (true, true, true) ∧
      (sides.map fun source => [1, 2, 3, 4].filter source.referencesField) =
        [[2, 3], [1, 4], [4]] := by
  native_decide

end A12Kernel.Conformance.ValueListCondition
