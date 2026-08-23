import A12Kernel.Elaboration.TimeInput

/-! # Time stored-input laws

The capsule's headline claim is universal rather than case-by-case: a Time cell has exactly **one**
formal cause available to it, so no stored text can produce the date finding that Date and DateTime
input reserve for a position below the Gregorian floor. -/

namespace A12Kernel

/-- Every Time cell this classifier *decides* carries either no finding or the single date-format
finding. A clock has no position in time, so the second cause its Date and DateTime siblings need is
unreachable here — and this is the statement that keeps a later widening from quietly introducing one.

Stated over stored text on purpose: an already-`rejected` raw cell propagates whatever cause an earlier
stage put there, and that cause is not this classifier's to constrain. -/
theorem timeInput_checkStored_singleCause
    (checked : CheckedTimeInputField) (text : String) :
    (checked.checkStored (.parsed text)).findings = [] ∨
      (checked.checkStored (.parsed text)).findings = [.dateFormat] := by
  by_cases hEmpty : text.isEmpty
  · simp [CheckedTimeInputField.checkStored, hEmpty]
  · cases hDecoded : decodeTimeLiteral? text with
    | none =>
        simp [CheckedTimeInputField.checkStored, hEmpty, hDecoded,
          BaseFormalCause.toFormalCause]
    | some clock =>
        simp [CheckedTimeInputField.checkStored, hEmpty, hDecoded]

/-- Present-empty stored text is never a formal rejection: emptiness is not invalidity, and the cell
stays physically present so a consumer can still distinguish it from absence. -/
@[simp] theorem timeInput_checkStored_presentEmpty
    (checked : CheckedTimeInputField) :
    checked.checkStored .presentEmpty =
      { rawPresent := true, parsed := none, findings := [] } := rfl

/-- Empty *parsed* text takes the same route as present-empty rather than failing to decode, which is
what keeps an empty cell from acquiring a cause on the way in. -/
@[simp] theorem timeInput_checkStored_parsed_empty
    (checked : CheckedTimeInputField) :
    checked.checkStored (.parsed "") =
      { rawPresent := true, parsed := none, findings := [] } := rfl

/-- A certified declaration retains the kernel's stored clock format, so a consumer never has to
re-derive which spelling this cell was decoded from. -/
theorem checkedTimeInputField_format_declared
    (checked : CheckedTimeInputField) :
    TimeTargetFormat.ofSource? checked.policy.format = some checked.format ∧
      checked.field.kind = .time :=
  ⟨checked.formatOwned, checked.kindOwned⟩

end A12Kernel
