import A12Kernel.Elaboration.Flat.Types
import A12Kernel.Elaboration.TimeLiteral
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.TemporalTarget

/-! # Checked Time stored input

Stored Time text is converted non-leniently against the declaration's format, and this capsule
classifies it for the only Time format the kernel stores. Its result is a `CheckedCell TimeOfDay`,
which is already the input every Time consumer reads, so nothing here widens the value domain.

**One cause covers every failure.** Measured, a Time field reports the *date-format* finding for a
component of the wrong width and for every out-of-range component alike — hour `24` included, which is
not an end-of-day spelling — and it never reports the date finding, because a clock has no position in
time to fall below a floor. That is the whole difference from `Date` and `DateTime` input, both of which
carry the Gregorian floor and therefore need two causes.

The lexical rule is **identical to the authored Time literal's**, so the two share one decoder rather
than agreeing by construction: three fixed two-digit ASCII components separated by colons, then the
range invariant the clock type already carries. Wider formats, a declaration whose format string is not
this one, zone resolution, and DateTime input remain separate — a temporal declaration's format is
checked against a kind-independent vocabulary, so a TIME field may legally declare a date format, and
such a declaration is refused certification here rather than silently read as a clock. -/

namespace A12Kernel

/-- Fail-closed reasons before a declaration can use the bounded Time input classifier. -/
inductive CanonicalTimeFieldError where
  | notTime (path : List String) (actual : FieldKind)
  | policyUnavailable (path : List String)
  /-- The declaration is a Time field whose declared format is not the stored clock format. This is
  reachable rather than defensive: the model gate admits any vocabulary format on any temporal kind. -/
  | unsupportedFormat (path : List String) (format : String)
  deriving Repr, DecidableEq

/-- One Time declaration whose kind, complete clock component shape, and storage format are
model-owned. Addressing remains consumer-owned. -/
structure CheckedTimeInputField where
  private mk ::
  declaration : FlatFieldDecl
  field : FlatTemporalField
  policy : TemporalTargetPolicy
  format : TimeTargetFormat
  fieldOwned : declaration.toTemporalField? = some field
  policyOwned : declaration.toTemporalTargetPolicy? = some policy
  kindOwned : field.kind = .time
  formatOwned : TimeTargetFormat.ofSource? policy.format = some format

/-- Certify one bounded Time input declaration without imposing an addressing shape. -/
def certifyTimeInputField (declaration : FlatFieldDecl) :
    Except CanonicalTimeFieldError CheckedTimeInputField :=
  match hField : declaration.toTemporalField? with
  | none => .error (.notTime declaration.path declaration.policy.kind)
  | some field =>
      if hKind : field.kind = .time then
        match hPolicy : declaration.toTemporalTargetPolicy? with
        | none => .error (.policyUnavailable declaration.path)
        | some policy =>
            match hFormat : TimeTargetFormat.ofSource? policy.format with
            | none => .error (.unsupportedFormat declaration.path policy.format)
            | some format => .ok {
                declaration
                field
                policy
                format
                fieldOwned := hField
                policyOwned := hPolicy
                kindOwned := hKind
                formatOwned := hFormat }
      else
        .error (.notTime declaration.path declaration.policy.kind)

/-- Classify stored Time text under its certified declaration. Present-empty stays present and
value-free; every other failure is the one measured cause.

The receiver is required but unread: `TimeTargetFormat` has exactly one constructor, so certification
has already decided the whole lexical rule and there is nothing left to consult per call. -/
def CheckedTimeInputField.checkStored (_checked : CheckedTimeInputField)
    (raw : RawCell String) : CheckedCell TimeOfDay :=
  checkRawCellWith (fun text =>
    if text.isEmpty then
      .ok none
    else
      match decodeTimeLiteral? text with
      | none => .error .dateFormat
      | some clock => .ok (some clock)) raw

/-- Read one classified Time cell at an evaluation phase, which is where the same formal invalidity
becomes validation's unknown or computation's poison. -/
def CheckedTimeInputField.observe (checked : CheckedTimeInputField)
    (phase : Phase) (raw : RawCell String) : CellObservation TimeOfDay :=
  observeCell phase (checked.checkStored raw)

end A12Kernel
