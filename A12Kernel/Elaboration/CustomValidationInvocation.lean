import A12Kernel.Elaboration.CheckedIndexPreliminary
import A12Kernel.Elaboration.ValidationRelevance
import A12Kernel.Semantics.CustomCondition

/-! # The custom-condition callback's inputs over a checked document

One construction of the four callback channels for every validation carrier that reaches a
`CustomCondition` leaf, ordinary and parallel alike, so their formal-invalid payloads cannot differ
([spec/11 §14](../../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch)).
Each carrier supplies its own error pointer.
-/

namespace A12Kernel

abbrev CustomValidationInvocation (model : FlatModel) :=
  CustomConditionInvocation (CheckedDocument model) ValidationRelevanceScope (List CellAddr)

abbrev CustomValidationRegistry (model : FlatModel) :=
  CustomConditionRegistry (CustomValidationInvocation model)

/-- The callback's four channels at one evaluation point, shared by every carrier that reaches a custom leaf. Formal findings are never filtered by callback-hidden dependencies; generated formal failures augment the base findings (spec/11 §14). A partial call formally checks only the cells it covers, so a malformed cell outside its relevant set is not among them (peer KF52; row `r4-formal` of the custom-condition call capture). -/
def CustomValidationInvocation.ofDocument (document : CheckedDocument model)
    (relevance : CustomConditionRelevance ValidationRelevanceScope) (errorPointer : MessagePointer)
    (generatedFormalFailures : List CellAddr := []) : CustomValidationInvocation model :=
  let checked (address : CellAddr) : Bool := match relevance, model.lookupUniqueId address.field with
    | .all, _ => true
    | .partialEntities scope, .ok declaration =>
        scope.coversCell model declaration.path (declaration.repeatableScope.zip address.path)
    | .partialEntities _, .error _ => false
  { data := document
    relevance
    formallyIncorrect := ((document.checkedCells.filterMap fun cell =>
      if cell.cell.findings.isEmpty || !checked cell.address then none else some cell.address) ++
        generatedFormalFailures).eraseDups
    errorPointer }

/-- The formal failures a partial call generates beyond the base findings: the index preliminary's findings and every required evaluation that fired. -/
def CheckedPartialPreliminary.generatedFormalFailures (preliminary : CheckedPartialPreliminary model) :
    List CellAddr :=
  preliminary.index.findings.map (·.address) ++ preliminary.required.filterMap fun evaluation =>
    match evaluation.verdict with
    | .fired _ => some evaluation.address
    | _ => none

end A12Kernel
