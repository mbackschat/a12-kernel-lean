import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Core

/-! # Shared ordinary repeatable runtime fixtures -/

namespace A12Kernel.Conformance.ValidationRule.OrdinarySupport

open A12Kernel

def ordinaryIterationData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [2] },
      { group := 10, path := [1] },
      { group := 20, path := [2, 1] },
      { group := 20, path := [1, 1] }]
    cells := [{
      address := { field := outerAmount.id, path := [1] }
      stored := "1"
      raw := .parsed (.num 1)
    }] }

def evalOrdinaryRule? (rule :
    CheckedResolvedValidationRule ordinaryIterationModel)
    (data : DocumentData) : Option (List (Env × FlatRuleOutcome)) := do
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  (rule.evalOrdinaryRepeatableFull checked).toOption

def classifiedCell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

end A12Kernel.Conformance.ValidationRule.OrdinarySupport
