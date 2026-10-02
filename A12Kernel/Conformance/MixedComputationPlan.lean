import A12Kernel.Elaboration.MixedComputationPlan

/-! # One plan over fixed and repeatable targets of different kinds

The case locks the plan's overlay at the seam no component plan reaches alone: a row String target
read by a fixed whole-document step. Authored reader-first, the plan runs the row constant first, and
the reader sees the constant at its exact row rather than the stale stored text there.
-/

namespace A12Kernel.Conformance.MixedComputationPlan

open A12Kernel

private def label : FlatFieldDecl :=
  { id := 1, groupPath := ["Probe", "Tasks"], name := "Label", policy := { kind := .string }
    repeatableScope := [10] }

private def note : FlatFieldDecl :=
  { id := 2, groupPath := ["Probe", "Store"], name := "Note", policy := { kind := .string } }

private def model : FlatModel :=
  { fields := [label, note]
    repeatableGroups := [{ level := 10, path := ["Probe", "Tasks"], repeatability := some 3 }] }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption.get
    (by native_decide)

/-- One task row whose `Label` stores a stale `OLD`. -/
private def document? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := [{ address := { field := label.id, path := [1] }, stored := "OLD"
                raw := .parsed (.str "OLD") }] }).toOption

private def labels : SurfaceStarFieldPath :=
  { base := .absolute, groups := [{ name := "Probe" }, { name := "Tasks", starred := true }]
    field := "Label" }

private def steps? : Option (List (MixedComputationStep model builtinStringPatternCompiler)) := do
  let reader ← (checkStringFirstFilledComputation model ["Probe"] note.id (.star labels)).toOption
  let constant ← (checkRepeatableStringConstantComputation model ["Probe"] label.id "NEW").toOption
  pure [.document (.ofStringFirstFilled reader), .rows (.ofRepeatableStringConstant constant)]

private def run? : Option (List (CellAddr × Option String)) := do
  let plan ← (certifyMixedComputationPlan (← steps?)).toOption
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } prepared.patterns (← document?)).toOption
  pure (outcomes.filterMap fun
    | .document address outcome => some (address, outcome.storedText?)
    | _ => none)

/- The reader is authored first and still runs second, and it reads the constant, not the stale `OLD`
an account reading the stored document would return. -/
example : run? = some [({ field := label.id, path := [1] }, some "NEW"), ({ field := note.id, path := [] }, some "NEW")] := by
  native_decide

end A12Kernel.Conformance.MixedComputationPlan
