import A12Kernel.Elaboration.MixedComputationPlan

/-! # One plan over fixed and repeatable targets of different kinds

The cases lock the plan's overlay at the seams no component plan reaches alone: a row String target
read by a fixed whole-document step, and a row String step read by a Number row table. Authored
reader-first, the plan runs the producer first, and the reader sees the computed value at its exact
row rather than the stale stored text there.
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

private def amount : FlatFieldDecl :=
  { id := 3, groupPath := ["Probe", "Tasks"], name := "Amount"
    policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10] }

private def back : FlatFieldDecl :=
  { id := 4, groupPath := ["Probe", "Tasks"], name := "Back"
    policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10] }

/-- A digits-only String, the source shape `FieldValueAsNumber` converts. -/
private def digits : FlatFieldDecl :=
  { id := 5, groupPath := ["Probe", "Tasks"], name := "Digits", policy := { kind := .string }
    stringPolicy := { maxLength := some 15 }, stringPatternSource := some asciiDigitsPatternSource
    repeatableScope := [10] }

private def chainModel : FlatModel :=
  { fields := [amount, back, digits]
    repeatableGroups := [{ level := 10, path := ["Probe", "Tasks"], repeatability := some 3 }] }

private def chainPrepared : PreparedFlatStringContext chainModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler chainModel).toOption.get
    (by native_decide)

/-- Two task rows, `Amount` 7 and 13, each `Digits` storing a stale `90`. -/
private def chainDocument? : Option (CheckedDocument chainModel) :=
  (checkDocument chainPrepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
    cells := [1, 2].flatMap fun row =>
      [{ address := { field := amount.id, path := [row] }, stored := toString (if row == 1 then 7 else 13)
         raw := .parsed (.num (if row == 1 then 7 else 13)) },
       { address := { field := digits.id, path := [row] }, stored := "90", raw := .parsed (.str "90") }] }).toOption

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

/-- `Back = FieldValueAsNumber(Digits)` authored ahead of `Digits = FieldValueAsString(Amount)`. -/
private def chainRun? : Option (List (CellAddr × String)) := do
  let reader ← (elaborateNumericTargetComputationTable chainModel ["Probe", "Tasks"] back.id
    [(none, .atom (.fieldValueAsNumber (.direct (bare "Digits"))))] (targetScope := .row)).toOption
  let producer ← (checkAddressedFieldValueAsString chainModel ["Probe", "Tasks"] digits.id (bare "Amount")).toOption
  let step ← CheckedRowComputationStep.ofAddressedFieldValueAsString? producer
  let plan ← (certifyMixedComputationPlan [.number reader, .rows (step builtinStringPatternCompiler)]).toOption
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } chainPrepared.patterns (← chainDocument?)).toOption
  pure (outcomes.filterMap fun
    | .number { targetField, outcome := .accepted stored, .. } => some (targetField, stored.render)
    | _ => none)

/- The Number reader runs after the row producer and reads its rendering at each exact row, `7` and
`13`, not the stale `90` both rows store. -/
example : chainRun? = some [({ field := back.id, path := [1] }, "7"), ({ field := back.id, path := [2] }, "13")] := by
  native_decide

end A12Kernel.Conformance.MixedComputationPlan
