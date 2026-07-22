import A12Kernel.Semantics.PartialValidation

/-! # Flat, nonrepeatable partial-validation separating cases -/

namespace A12Kernel.Conformance.PartialValidation

open A12Kernel

private def errorField : FlatBooleanField := { id := 0 }
private def otherField : FlatBooleanField := { id := 1 }

private def filledContext : FlatContext where
  read id :=
    if id = errorField.id || id = otherField.id then
      formalCheck { kind := .boolean } (.parsed (.bool true))
    else formalCheck { kind := .boolean } .empty

private def errorFilled : FlatCondition := .fieldFilled (.boolean errorField)
private def otherFilled : FlatCondition := .fieldFilled (.boolean otherField)
private def bothFilled : FlatCondition := .and errorFilled otherFilled
private def eitherFilled : FlatCondition := .or errorFilled otherFilled
private def only (field : FieldId) : FlatRelevance := fun candidate => candidate == field
private def bothRelevant : FlatRelevance := fun candidate => candidate == errorField.id || candidate == otherField.id

example :
    bothFilled.evalPartial filledContext errorField.id bothRelevant .unfiltered =
        .evaluated (bothFilled.evalFull filledContext true) ∧
      bothFilled.evalPartial filledContext errorField.id (only errorField.id)
        .unfiltered =
        .evaluated .unknown ∧
      eitherFilled.evalPartial filledContext errorField.id (only errorField.id)
        .unfiltered =
        .evaluated (.fired .value) := by
  native_decide

private def temporalComponents : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := false, minute := false, second := false }

private def earlierDate : FlatTemporalField :=
  { id := 3, kind := .date, components := temporalComponents }

private def laterDate : FlatTemporalField :=
  { id := 4, kind := .date, components := temporalComponents }

private def temporalContext : FlatContext where
  read id :=
    if id = earlierDate.id then
      formalCheck { kind := .temporal .date temporalComponents }
        (.parsed (.temporal .date { epochMillis := 100999 }))
    else if id = laterDate.id then
      formalCheck { kind := .temporal .date temporalComponents }
        (.parsed (.temporal .date { epochMillis := 101000 }))
    else formalCheck { kind := .boolean } (.rejected .malformed)

private def earlierBeforeLater : FlatCondition :=
  .compare (.temporal .before (.fieldValue earlierDate) (.fieldValue laterDate))

/-! Both operands of a field-to-field comparison must be relevant; checking only the first read would expose an out-of-set value. -/
example :
    earlierBeforeLater.evalSelected temporalContext (only earlierDate.id) = .unknown ∧
      earlierBeforeLater.evalSelected temporalContext
        (fun id => id == earlierDate.id || id == laterDate.id) = .fired .value := by
  native_decide

/-! Masking alone would fire `Unknown Or True`; the independent error-field gate skips. -/
example :
    eitherFilled.evalSelected filledContext (only otherField.id) = .fired .value ∧
      eitherFilled.evalPartial filledContext errorField.id (only otherField.id)
        .unfiltered =
        .skipped := by
  native_decide

/-! Nearest non-law: relevant error-field gating does not make partial equal full. -/
example :
    (FlatCondition.compare (.boolean .equal otherField true)).evalPartial
        filledContext errorField.id (only errorField.id) .unfiltered =
          .evaluated .unknown ∧
      (FlatCondition.compare (.boolean .equal otherField true)).evalFull
        filledContext true = .fired .value := by
  native_decide

private def numberField : FlatNumberField :=
  { id := 2, info := { scale := 0, signed := false } }
private def emptyNumberContext : FlatContext where
  read _ := formalCheck { kind := .number numberField.info } .empty
private def emptyNumberIsZero : FlatCondition :=
  .compare (.number (.ordinary .equal) numberField 0)

/-! A relevant instance bypasses the ordinary full-validation content gate. -/
example :
    emptyNumberIsZero.evalPartial emptyNumberContext numberField.id
        (only numberField.id) .unfiltered = .evaluated (.fired .omission) ∧
      emptyNumberIsZero.evalFull emptyNumberContext false = .notFired := by
  native_decide

/-! A rule-level `Having` marker skips before relevance and condition evaluation. The full route still evaluates the same condition. -/
example :
    bothFilled.evalFull filledContext true = .fired .value ∧
      bothFilled.evalPartial filledContext errorField.id bothRelevant .filtered =
        .skipped := by
  native_decide

private def filledNumberContext : FlatContext where
  read id :=
    if id = numberField.id then
      formalCheck { kind := .number numberField.info } (.parsed (.num 2))
    else formalCheck { kind := .number numberField.info } .empty

private def numberGreaterThanZero : FlatCondition :=
  .compare (.number (.ordinary .greater) numberField 0)

/-! The early filter gate is not equality- or presence-specific. -/
example :
    numberGreaterThanZero.evalFull filledNumberContext true = .fired .value ∧
      numberGreaterThanZero.evalPartial filledNumberContext numberField.id
        (only numberField.id) .filtered = .skipped := by
  native_decide

end A12Kernel.Conformance.PartialValidation
