import A12Kernel.Elaboration.Flat.Types
import A12Kernel.Elaboration.TimeLiteral
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.TemporalTarget

/-! # Checked Time stored input

Stored clock text is converted non-leniently against the declaration's format, and this capsule
classifies any temporal field at the `HH:mm:ss` declaration, whatever its declared kind. Its result is a `CheckedCell TimeOfDay`,
which is already the input every Time consumer reads, so nothing here widens the value domain.

**One cause covers every failure in that certified clock profile.** Measured, the declaration reports the *date-format* finding for a
component of the wrong width and for every out-of-range component alike — hour `24` included, which is
not an end-of-day spelling — and it never reports the date finding, because this format carries no position in
time to fall below a floor. A field at a date-bearing declaration is outside this classifier and may
reach the date finding, whichever kind declares it; the format alone selects the cause set.

The lexical rule is **identical to the authored Time literal's**, so the two share one decoder rather
than agreeing by construction: three fixed two-digit ASCII components separated by colons, then the
range invariant the clock type already carries. Wider formats, a declaration whose format string is not
this one, zone resolution, and DateTime input remain separate.

**The declared kind is not read, and that is measured rather than chosen.** A temporal declaration's
format is checked against a kind-independent vocabulary, so a **DATE** field may legally declare
`HH:mm:ss`; the Kernel then classifies its stored text exactly as it classifies a TIME field's, over
the complete twelve-format vocabulary on all three date-bearing kinds
([inbound](../../docs/SOURCES.md#inbound-2026-09-05b)). A kind conjunct here left such a cell
classified by **no** classifier at all, so its text could not be classified rather than being
classified wrongly. The format is the whole gate, and it is what keeps the families disjoint: a
date-bearing spelling fails `TimeTargetFormat.ofSource?` and reaches its own classifier. -/

namespace A12Kernel

/-- Fail-closed reasons before a declaration can use the bounded Time input classifier. -/
inductive CanonicalTimeFieldError where
  /-- The declaration is not temporal at all. It carries the declared kind for the report, which is
  the one place that kind is still read — a diagnostic, never a gate. -/
  | notTime (path : List String) (actual : FieldKind)
  | policyUnavailable (path : List String)
  /-- The declaration is a Time field whose declared format is not the stored clock format. This is
  reachable rather than defensive: the model gate admits any vocabulary format on any temporal kind. -/
  | unsupportedFormat (path : List String) (format : String)
  deriving Repr, DecidableEq

/-- One declaration whose storage format is the stored clock, model-owned. The declared **kind** is
deliberately absent from this certificate: it is not part of the gate, so a proof of it would be a
theorem this project can state and the Kernel does not honour. Addressing remains consumer-owned. -/
structure CheckedTimeInputField where
  private mk ::
  declaration : FlatFieldDecl
  field : FlatTemporalField
  policy : TemporalTargetPolicy
  format : TimeTargetFormat
  fieldOwned : declaration.toTemporalField? = some field
  policyOwned : declaration.toTemporalTargetPolicy? = some policy
  formatOwned : TimeTargetFormat.ofSource? policy.format = some format

/-- Certify one bounded Time input declaration without imposing an addressing shape. -/
def certifyTimeInputField (declaration : FlatFieldDecl) :
    Except CanonicalTimeFieldError CheckedTimeInputField :=
  match hField : declaration.toTemporalField? with
  | none => .error (.notTime declaration.path declaration.policy.kind)
  | some field =>
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
              formatOwned := hFormat }

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
