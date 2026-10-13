import A12Kernel.Elaboration.NumericValidation.EntityComparison
import A12Kernel.Conformance.ValidationRule.OrdinarySupport

/-! # Rule comparisons over entity lists, elaborated from their surface

`elaborateEntityNumericComparison` builds the ordered comparison that the entity locks beside it
assemble by hand. These cases lock that the two agree on a rule's verdicts and that the forms other carriers own, a
plain field list and the filled-group count, are refused here.
-/

namespace A12Kernel.Conformance.ValidationRule.OrdinaryEntitySurface

open A12Kernel
open A12Kernel.Conformance.ValidationRule.OrdinarySupport

private def innerStarSum : SurfaceNumericComputationAtom :=
  .numeric (.aggregate .sum { first := .star deeperInnerAmountStar, rest := [] })

/-- `OuterAmount + Sum(Items*/InnerAmount) > 5`, the hand-assembled `outerWithInnerAggregate`. -/
private def surfaceRule? : Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let numeric ← (elaborateEntityNumericComparison ordinaryIterationModel ["Order", "Sections"]
    (.ordinary .greater)
    (.binary .add (.atom (.numeric (.field (ordinaryPath ["Order", "Sections"] "OuterAmount"))))
      (.atom innerStarSum))
    (.literal { value := 5, authoredScale := 0 })).toOption
  let condition ← (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition outerAmount.id
    "outerWithInnerAggregate" .error { parts := [] }).toOption

private def data (outer : Option Rat) (inner : List (RowIndex × Rat)) : DocumentData :=
  { instantiatedRows := { group := 10, path := [1] } ::
      inner.map fun (row, _) => { group := 20, path := [1, row] }
    cells := (outer.toList.map fun value =>
        classifiedCell outerAmount.id [1] (toString value) (.parsed (.num value))) ++
      inner.map fun (row, value) =>
        classifiedCell innerAmount.id [1, row] (toString value) (.parsed (.num value)) }

private def verdicts? (rule? : Option (CheckedResolvedValidationRule ordinaryIterationModel))
    (document : DocumentData) : Option (List Verdict) := do
  let outcomes ← evalOrdinaryRule? (← rule?) document
  pure (outcomes.map (·.2.verdict))

/- The surface route and the hand-assembled one agree where the sum crosses the threshold, where it
does not, and where the outer operand is absent. -/
example :
    [data (some 1) [(1, 3), (2, 4)], data (some 1) [(1, 1), (2, 2)], data none [(1, 3), (2, 4)]].all
      (fun document => verdicts? surfaceRule? document == verdicts? outerWithInnerAggregateRule? document &&
        (verdicts? surfaceRule? document).isSome) := by
  native_decide

/- A list of plain fields only stays with the scalar comparison: the addressed scope admits it in
neither atom form, so this entry point refuses it, while a starred list is an entity aggregate. -/
private def number (id : FieldId) (name : String) : FlatFieldDecl :=
  { id, groupPath := ["Order"], name, policy := { kind := .number { scale := 0, signed := true } } }

private def leftAtomKind? (model : FlatModel) (rowGroup : GroupPath)
    (atom : SurfaceNumericComputationAtom) : String :=
  match elaborateEntityNumericComparison model rowGroup
      (.ordinary .greater) (.atom atom) (.literal { value := 5, authoredScale := 0 }) with
  | .error .incoherent => "incoherent"
  | .error _ => "refused"
  | .ok checked => match checked.core.left with
    | .atom (.aggregate _ _) => "entity"
    | _ => "other"

example :
    (leftAtomKind? { fields := [number 1 "A", number 2 "B"] } ["Order"] (.numeric (.aggregate .sum
        { first := .field (ordinaryPath ["Order"] "A") .stored
          rest := [.field (ordinaryPath ["Order"] "B") .stored] })),
     leftAtomKind? ordinaryIterationModel ["Order", "Sections"] innerStarSum) =
      ("incoherent", "entity") := by
  native_decide

/- A filled-group count reuses the count's own atoms rather than acquiring a second representation,
so an empty list meets the scalar count's own arity refusal. -/
example :
    (match elaborateEntityNumericComparison ordinaryIterationModel ["Order", "Sections"]
        (.ordinary .greater) (.atom (.numeric (.filledGroupCount [])))
        (.literal { value := 0, authoredScale := 0 }) with
      | .error (.ordinary .groupCountNeedsMultipleOperands) => true
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.ValidationRule.OrdinaryEntitySurface
