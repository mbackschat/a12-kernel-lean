import A12Kernel.Elaboration.ConstructedDateEvaluation

/-! # Checked constructed-Date execution locks -/

namespace A12Kernel.Conformance.ConstructedDateEvaluation

open A12Kernel

private def componentField
    (id : FieldId) (constraints : NumericTargetConstraints) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"DateComponent{id}"
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := constraints
}

private def dateModel (zoneId : String := "UTC") : FlatModel := {
  fields := [
    componentField 1 { maximum := some 31 },
    componentField 2 { maximum := some 12 },
    componentField 3 { maxStoredLength := some 4 }]
  timeZoneId := zoneId
}

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument (dateModel "UTC")) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler (dateModel "UTC")).toOption
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  } |>.toOption

private def numberCell (field : FieldId) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw
}

private def evaluate? (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateComponents (dateModel "UTC") 1 2 3).toOption
  let input ← document? cells
  checked.evaluate .validation input |>.toOption

private def validVerdict? (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateComponents (dateModel "UTC") 1 2 3).toOption
  let input ← document? cells
  checked.evaluateValid .validation input |>.toOption

private def invalidVerdict? (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateComponents (dateModel "UTC") 1 2 3).toOption
  let input ← document? cells
  checked.evaluateInvalid .validation input |>.toOption

private def numericPart? (part : DateNumericPart)
    (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateComponents (dateModel "UTC") 1 2 3).toOption
  let input ← document? cells
  checked.evaluateNumericPart part .validation input |>.toOption

/- Checked execution preserves the default-cutover identity through all three literal
   calendar shifts. -/
example :
    let source := evaluate? [
      numberCell 1 "4" (.parsed (.num 4)),
      numberCell 2 "10" (.parsed (.num 10)),
      numberCell 3 "1582" (.parsed (.num 1582))]
    source.bind (·.addLegacyDays? 1) =
        some (.resolved (.real {
          year := 1582, month := 10, day := 15 })) ∧
      source.bind (·.addLegacyMonths? (-1)) =
        some (.resolved (.real {
          year := 1582, month := 9, day := 4 })) ∧
      source.bind (·.addLegacyYears? 1) =
        some (.resolved (.real {
          year := 1583, month := 10, day := 4 })) := by
  native_decide

/- A present cutover-hole label is unreal, while an empty component is incomplete. -/
example :
    evaluate? [
        numberCell 1 "10" (.parsed (.num 10)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.resolved .unreal) ∧
      evaluate? [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.resolved .incomplete) := by
  native_decide

/- Formal failure retains the first authored component's exact cause. -/
example :
    evaluate? [
      numberCell 1 "bad" (.rejected .malformed),
      numberCell 2 "100" (.rejected .declaredConstraint)] =
        some (.unavailable .malformed) := by
  native_decide

/- Cause-free construction UNKNOWN cannot replace the checked wrapper: two formal causes
   remain distinguishable after the same shift. -/
example :
    ConstructedDateObservation.addLegacyDays? (.unavailable .malformed) 1 ≠
      ConstructedDateObservation.addLegacyDays?
        (.unavailable .declaredConstraint) 1 := by
  native_decide

/- Checked `Valid` and `Invalid` reuse the reason-bearing polarity table while retaining
   a formal component cause outside `Verdict`. -/
example :
    validVerdict? [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.fired .value)) ∧
      invalidVerdict? [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.fired .omission)) ∧
      invalidVerdict? [
        numberCell 1 "10" (.parsed (.num 10)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.fired .value)) ∧
      validVerdict? [
        numberCell 1 "bad" (.rejected .malformed)] =
          some (.error .malformed) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

/- Checked component extraction retains present versus fillable zero and the exact
   formal cause without adding a second numeric result family. -/
example :
    numericPart? .day [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.value 4 false)) ∧
      numericPart? .month [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.value 0 true)) ∧
      numericPart? .year [
        numberCell 1 "10" (.parsed (.num 10)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.value 0 false)) ∧
      numericPart? .quarter [
        numberCell 1 "bad" (.rejected .declaredConstraint)] =
          some (.error .declaredConstraint) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

/- A forged cause-free UNKNOWN is distinguishable from a checked formal cause. -/
example :
    ConstructedDateObservation.numericPart (.resolved .unknown) .day =
        .ok .unavailable ∧
      ConstructedDateObservation.numericPart
        (.unavailable .malformed) .day = .error .malformed := by
  constructor <;> rfl

end A12Kernel.Conformance.ConstructedDateEvaluation
