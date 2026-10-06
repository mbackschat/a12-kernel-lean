import A12Kernel.Elaboration.ValidationCondition.Assembly

namespace A12Kernel.Conformance.ValuesNotUniqueCondition

open A12Kernel

private def model : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Form"], name := "A", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 2, groupPath := ["Form"], name := "B", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 3, groupPath := ["Form"], name := "Bad", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 4, groupPath := ["Form"], name := "X", policy := { kind := .string } },
      { id := 5, groupPath := ["Form"], name := "Y", policy := { kind := .string } },
      { id := 6, groupPath := ["Form"], name := "D", policy := { kind := .temporal .date .fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { id := 7, groupPath := ["Form"], name := "E", policy := { kind := .temporal .date .fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } }] }

private def direct (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field := name }

private def sources : List (CheckedValuesNotUniqueCondition model) :=
  [(elaborateNumberValuesNotUniqueSource model ["Form"]
      { first := direct "Bad", rest := [direct "A", direct "B"] }).toOption.map .number,
   (elaborateTokenValuesNotUniqueSource model ["Form"]
      { first := direct "X", rest := [direct "Y"] }).toOption.map .token,
   (elaborateTemporalValuesNotUniqueSource model ["Form"]
      { first := direct "D", rest := [direct "E"] }).toOption.map .temporal].filterMap id

private def rejectsSoleValueListCertificate : Bool :=
  match elaborateNumberEntityValueListSource model ["Form"]
      { quantifier := .atLeastOne, fields := { first := direct "A", rest := [] }
        values := { first := direct "B", rest := [] } } with
  | .error _ => false
  | .ok source => !(CheckedValidationCondition.fromValuesNotUnique ["Form"]
      (.number source.fields)).isOk

example : rejectsSoleValueListCertificate := by native_decide

private def document? : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let date : RawCell := .parsed (.temporal (.date {
    instant := { epochMillis := 0 }, parts := { year := 1970, month := 1, day := 1 }
    basis := .storedGregorian }))
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      { address := { field := 1, path := [] }, stored := "1", raw := .parsed (.num 1) },
      { address := { field := 2, path := [] }, stored := "1", raw := .parsed (.num 1) },
      { address := { field := 3, path := [] }, stored := "bad", raw := .rejected .malformed },
      { address := { field := 4, path := [] }, stored := "x", raw := .parsed (.str "x") },
      { address := { field := 5, path := [] }, stored := "x", raw := .parsed (.str "x") },
      { address := { field := 6, path := [] }, stored := "1970-01-01", raw := date },
      { address := { field := 7, path := [] }, stored := "1970-01-01", raw := date }] }).toOption

private def outcomes : Option (List (Option Verdict × Bool × Bool × Option Verdict)) := do
  let document ← document?
  let context : AddressedValidationEvaluationContext model :=
    { scalar := { fields := document.flatContext, groups := .unavailable }
      outer := [], input := .checked document }
  let legacy := { context with input := .legacy document.source.toDocument fun _ => document.flatContext.read }
  let partialContext := { context with input := .partialView document fun _ _ => pure none }
  let refuses : Except CheckedAddressingError Verdict → Bool
    | .error (.checkedDocumentRequired []) => true
    | _ => false
  sources.mapM fun source => do
    let checked ← (CheckedValidationCondition.fromValuesNotUnique ["Form"] source).toOption
    let absent : ValidationCondition model := .leaf (.flat (.fieldNotFilled (.string { id := 4 })))
    pure ((checked.core.evalAddressed context).toOption,
      refuses (checked.core.evalAddressed legacy),
      refuses (checked.core.evalAddressed partialContext),
      (ValidationCondition.evalAddressed (.and absent checked.core) legacy).toOption)

example : sources.length = 3 ∧ outcomes = some (List.replicate 3
    (some (.fired .value), true, true, some .notFired)) := by
  native_decide

example : (sources.map fun source =>
    ((ValidationConditionLeaf.valuesNotUnique source).requiresAddressedValidation,
     (ValidationConditionLeaf.valuesNotUnique source).supportsAddressedPartial,
     (ValidationConditionLeaf.valuesNotUnique source).canFireOnEmpty)) =
      [(true, true, false), (true, true, false), (true, false, false)] ∧
    (sources.map fun source => [1, 2, 3, 4, 5, 6, 7].filter source.referencesField) =
      [[1, 2, 3], [4, 5], [6, 7]] := by
  native_decide

end A12Kernel.Conformance.ValuesNotUniqueCondition
