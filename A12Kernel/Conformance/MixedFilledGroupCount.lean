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

private def fieldN : FlatFieldDecl := {
  id := 3
  groupPath := ["Probe", "G1", "Nested"]
  name := "N"
  policy := { kind := .string }
  repeatableScope := [11]
}

private def fieldI : FlatFieldDecl := {
  id := 4
  groupPath := ["Probe", "Rows", "Inner"]
  name := "I"
  policy := { kind := .string }
  repeatableScope := [10, 12]
}

private def fieldO : FlatFieldDecl := {
  id := 5
  groupPath := ["Probe", "Other"]
  name := "O"
  policy := { kind := .string }
  repeatableScope := [13]
}

private def model : FlatModel := {
  fields := [fieldA, fieldR, fieldN, fieldI, fieldO]
  repeatableGroups := [
    { level := 10, path := ["Probe", "Rows"], repeatability := some 3 },
    { level := 11, path := ["Probe", "G1", "Nested"], repeatability := some 2 },
    { level := 12, path := ["Probe", "Rows", "Inner"], repeatability := some 2 },
    { level := 13, path := ["Probe", "Other"], repeatability := some 2 }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def fixedOperand : SurfaceGroupCountOperand :=
  .fixed (.path { base := .absolute, groups := ["Probe", "G1"] })

private def starredOperand : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := ["Probe", "Rows"] }

/-- A star strictly inside the fixed member's group, for the containment pair. -/
private def nestedStar : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := ["Probe", "G1", "Nested"] }

/-- A second, disjoint star, for the two-star sum. -/
private def otherStar : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := ["Probe", "Other"] }

/-- A star strictly inside another star's group, for the star-versus-star containment pair. -/
private def innerStar : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := ["Probe", "Rows", "Inner"] }

private def kernelCode? (operands : List SurfaceGroupCountOperand) : Option String :=
  match elaborateMixedFilledGroupCountComparison model ["Probe"] operands
      NumericComparisonOp.less 3 with
  | .error cause =>
      (NumericValidationElabError.groupCountDiagnostic? cause).map
        KernelStaticDiagnostic.kernelCode
  | .ok _ => none

private def comparison? (operands : List SurfaceGroupCountOperand) :
    Option (CheckedOrderedNumericComparison model) :=
  (elaborateMixedFilledGroupCountComparison model ["Probe"] operands
    NumericComparisonOp.less 3).toOption

private def atomOf? (operands : List SurfaceGroupCountOperand) :
    Option (OrderedNumericValidationAtom model) := do
  let comparison ← comparison? operands
  match comparison.core.left with
  | .atom source => some source
  | _ => none

private def atom? : Option (OrderedNumericValidationAtom model) :=
  atomOf? [fixedOperand, starredOperand]

/-- The fixed member's own presence state, supplied the way the checked-document boundary supplies
it. `errored` adds a malformed sibling beside the content cell, which is what the shared
unavailability rule reads; nonrelevant coverage is not this carrier's subject. -/
private def fixedState (content : Bool) (errored : Bool := false) : GroupPresenceState :=
  ({ descendantCells :=
       formalCheck { kind := .string }
           (if content then .parsed (.str "a") else .empty) ::
         (if errored then
            [formalCheck { kind := .number { scale := 0, signed := false } }
              (.rejected .malformed)]
          else [])
     hasInstantiatedRow := false
     structuralError := false
     relevance := .fullyRelevant } : ResolvedGroupPresenceInput).derive

private def cell (path : List Nat) : ClassifiedCellInput :=
  { address := { field := fieldR.id, path }
    stored := "r"
    raw := .parsed (.str "r") }

private def countWith (source : Option (OrderedNumericValidationAtom model))
    (content : Bool) (instantiated : List RowAddr)
    (filled : List (List Nat) := []) (errored : Bool := false) :
    Option NumericArithmeticOutcome := do
  let atom ← source
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := instantiated
    cells := filled.map cell }).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := document.flatContext
      groups := fun path =>
        if path == ["Probe", "G1"] then some (fixedState content errored) else none }
    outer := []
    input := .checked document }
  match atom.resolveAddressed context with
  | .ok inner => inner.toOption
  | .error _ => none

private def rowsUpTo (count : Nat) : List RowAddr :=
  (List.range count).map fun index => { group := 10, path := [index + 1] }

private def count (content : Bool) (rows : Nat)
    (filled : List (List Nat) := []) (errored : Bool := false) :
    Option NumericArithmeticOutcome :=
  countWith atom? content (rowsUpTo rows) filled errored

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

/- Containment between any two members is a duplicate, whichever is starred and in whichever order,
and it carries `MVK_DUPLICATE_PARAM2` rather than the equal-paths class. Two **stars naming the same
group** are admitted instead and count that group once per position, which is the exception that
makes this a containment rule rather than a distinctness rule. Measured on kernel 30.8.1. -/
example : (kernelCode? [fixedOperand, nestedStar],
    kernelCode? [nestedStar, fixedOperand],
    kernelCode? [starredOperand, innerStar],
    (comparison? [starredOperand, starredOperand]).isSome,
    (comparison? [nestedStar, starredOperand]).isSome) =
    (some "MVK_DUPLICATE_PARAM2", some "MVK_DUPLICATE_PARAM2",
     some "MVK_DUPLICATE_PARAM2", true, true) := by
  native_decide

private def otherRows (count : Nat) : List RowAddr :=
  (List.range count).map fun index => { group := 13, path := [index + 1] }

/- Two stars sum per member and their capacities sum too: a `max 3` beside a `max 2` counts three at
two-plus-one rows and is closed only at five. The **same** star twice double-counts rather than
collapsing to one group — two rows count four and the extent is six, not three — so the fold is per
position and so is the extent. That pair is what separates a per-position sum from a per-group one,
and both halves are measured on kernel 30.8.1 across both codegen strategies. -/
example : (countWith (atomOf? [starredOperand, otherStar]) false
      (rowsUpTo 2 ++ otherRows 1),
    countWith (atomOf? [starredOperand, otherStar]) false (rowsUpTo 3 ++ otherRows 2),
    countWith (atomOf? [starredOperand, starredOperand]) false (rowsUpTo 2),
    countWith (atomOf? [starredOperand, starredOperand]) false (rowsUpTo 3)) =
    (some (.value 3 { canGrow := true, canShrink := false }),
     some (.value 5 { canGrow := false, canShrink := false }),
     some (.value 4 { canGrow := true, canShrink := false }),
     some (.value 6 { canGrow := false, canShrink := false })) := by
  native_decide

/- Placement admits the star from an ancestor of its own group, which is the only shape measured. -/
example : (comparison? [fixedOperand, starredOperand]).isSome = true := by
  native_decide

/- The mixed carrier inherits the shared unavailability rule, and the kernel confirms both of its
legs on this very shape. A fixed member whose content is already admitted keeps contributing its one
however its other descendants failed; a fixed member whose only non-empty descendant is malformed
takes the whole mixed count with it rather than contributing zero. The middle row is the separator —
the same document with the malformed sibling removed — so the second row's absence is the error and
not the empty content. Measured on both codegen strategies at the [unavailability
checkpoint](../../docs/SOURCES.md#src-group-count-unavailability). -/
example : (count true 2 (errored := true), count false 2, count false 2 (errored := true)) =
    (some (.value 3 { canGrow := true, canShrink := false }),
     some (.value 2 { canGrow := true, canShrink := false }),
     none) := by
  native_decide

/- **Containment is checked before rootness, and the order is measured.** A root beside its own
descendant draws the overlap class rather than the root class, in either operand order, exactly as
the fixed-only list does. The root class is reserved for a root beside a *disjoint* operand, which
this fixture's single root cannot express — the [list-extent checkpoint](../../docs/SOURCES.md#src-group-count-list-extent)
carries that row on a two-root model. Running the gates the other way round reports a root the author
must remove where the Kernel reports an overlap they must resolve. -/
example : (kernelCode? [.fixed (.path { base := .absolute, groups := ["Probe"] }),
      starredOperand],
    kernelCode? [starredOperand,
      .fixed (.path { base := .absolute, groups := ["Probe"] })]) =
    (some "MVK_DUPLICATE_PARAM2", some "MVK_DUPLICATE_PARAM2") := by
  native_decide

/- Arity above the measured pair is admitted, mixed as well as fixed, and the admission does not
depend on where the star sits in the list. The gate is a minimum of two operands, not an exact pair;
the Kernel admits three- and four-operand lists on both shapes. -/
example : ((comparison? [fixedOperand, starredOperand, otherStar]).isSome,
    (comparison? [fixedOperand, otherStar, starredOperand]).isSome,
    (comparison? [starredOperand, fixedOperand, otherStar]).isSome) =
    (true, true, true) := by
  native_decide

end A12Kernel.Conformance.MixedFilledGroupCount
