import A12Kernel.Elaboration.NumericValidation.Resolution
import A12Kernel.Elaboration.NumericValidation.Evaluation
import A12Kernel.Elaboration.CheckedDocument

/-! # Mixed validation `NumberOfFilledGroups` locks

The Kernel rows behind these cases are the [list-extent
checkpoint](../../docs/SOURCES.md#src-group-count-list-extent).
-/

namespace A12Kernel.Conformance.MixedFilledGroupCount

open A12Kernel

private def fieldA : FlatFieldDecl := {
  id := 1
  groupPath := ["Probe", "G1"]
  name := "A"
  policy := { kind := .string }
}

private def fieldR : FlatFieldDecl := {
  id := 2
  groupPath := ["Probe", "Rows"]
  name := "R"
  policy := { kind := .string }
  repeatableScope := [10]
}

private def model : FlatModel := {
  fields := [fieldA, fieldR]
  repeatableGroups := [
    { level := 10, path := ["Probe", "Rows"], repeatability := some 3 }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def fixedOperand : SurfaceGroupCountOperand :=
  .fixed (.path { base := .absolute, groups := ["Probe", "G1"] })

private def starredOperand : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := ["Probe", "Rows"] }

private def comparison? (operands : List SurfaceGroupCountOperand) :
    Option (CheckedOrderedNumericComparison model) :=
  (elaborateMixedFilledGroupCountComparison model ["Probe"] operands
    NumericComparisonOp.less 3).toOption

private def atom? : Option (OrderedNumericValidationAtom model) := do
  let comparison ← comparison? [fixedOperand, starredOperand]
  match comparison.core.left with
  | .atom source => some source
  | _ => none

/-- The fixed member's own presence state, supplied the way the checked-document boundary supplies
it. Only its content varies here; erroneous and nonrelevant states belong to the shared group-count
unavailability rule and are not this carrier's subject. -/
private def fixedState (content : Bool) : GroupPresenceState :=
  ({ descendantCells :=
       [formalCheck { kind := .string }
         (if content then .parsed (.str "a") else .empty)]
     hasInstantiatedRow := false
     structuralError := false
     relevance := .fullyRelevant } : ResolvedGroupPresenceInput).derive

private def cell (path : List Nat) : ClassifiedCellInput :=
  { address := { field := fieldR.id, path }
    stored := "r"
    raw := .parsed (.str "r") }

private def count (content : Bool) (rows : Nat)
    (filled : List (List Nat) := []) : Option NumericArithmeticOutcome := do
  let atom ← atom?
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := (List.range rows).map fun index =>
      { group := 10, path := [index + 1] }
    cells := filled.map cell }).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := document.flatContext
      groups := fun path =>
        if path == ["Probe", "G1"] then some (fixedState content) else none }
    outer := []
    input := .checked document }
  match atom.resolveAddressed context with
  | .ok inner => inner.toOption
  | .error _ => none

/- Contributions add: the fixed member gives zero or one and the starred member gives its row count,
so one filled group beside zero, one, two, and three rows counts one, two, three, and four. The
extent is the sum of each member's own capacity, `1 + 3`, so only the last is closed — every earlier
count still has a legal move that falsifies a fired comparison. Measured on kernel 30.8.1 across both
codegen strategies, where those four documents type OMISSION, OMISSION, OMISSION, and VALUE. -/
example : (count true 0, count true 1, count true 2, count true 3) =
    (some (.value 1 { canGrow := true, canShrink := false }),
     some (.value 2 { canGrow := true, canShrink := false }),
     some (.value 3 { canGrow := true, canShrink := false }),
     some (.value 4 { canGrow := false, canShrink := false })) := by
  native_decide

/- A starred member counts **instantiated** rows, not filled ones, under an operator named
`NumberOfFilledGroups`. Two rows count two whether both, one, or neither carries a value, and a
single wholly empty row still counts. This is the separator every earlier document confounded by
filling each row it instantiated. -/
example : (count true 2 [[1], [2]], count true 2 [[1]], count true 2,
    count true 1) =
    (some (.value 3 { canGrow := true, canShrink := false }),
     some (.value 3 { canGrow := true, canShrink := false }),
     some (.value 3 { canGrow := true, canShrink := false }),
     some (.value 2 { canGrow := true, canShrink := false })) := by
  native_decide

/- Emptying the fixed member drops the total by exactly one and leaves the starred member's rows
untouched, which is what keeps the two contributions from reinterpreting each other. -/
example : (count false 2, count false 0) =
    (some (.value 2 { canGrow := true, canShrink := false }),
     some (.value 0 { canGrow := true, canShrink := false })) := by
  native_decide

/- The fixed-only list is refused here and stays on the established scalar carrier, so widening this
operator costs the already-measured form nothing. A single operand and a root-group member are
refused on the same terms the scalar list applies. -/
example : ((comparison? [fixedOperand]).isSome,
    (comparison? [fixedOperand, fixedOperand]).isSome,
    (comparison? [starredOperand]).isSome,
    (comparison? [.fixed (.path { base := .absolute, groups := ["Probe"] }),
      starredOperand]).isSome) =
    (false, false, false, false) := by
  native_decide

/- Placement admits the star from an ancestor of its own group, which is the only shape measured. -/
example : (comparison? [fixedOperand, starredOperand]).isSome = true := by
  native_decide

end A12Kernel.Conformance.MixedFilledGroupCount
