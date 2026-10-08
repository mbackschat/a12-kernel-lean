import A12Kernel.Elaboration.FullDateInput
import A12Kernel.Semantics.PartialDateInput

/-! # Checked partially known Date stored input

A Date declaration whose precision admits omissions stores a **literal zero component in a monotone
suffix**: an omitted day, an omitted month with the day also omitted, or an omitted year with both
also omitted. This capsule classifies such stored text under its certified declaration, producing
either one admitted value of the shared partial-Date domain or the exact formal cause.

**The two causes partition on a measured boundary, and it is not the obvious one.** A spelling or
calendar question is `dateFormat`: a wrong component width or separator count, and — measured — an
unreal calendar date among the value's *present* components, including an impossible month standing
beside an omitted day. An omission or position-in-time question is `dateInvalid`: a zero pattern that
is not a monotone suffix, a suffix deeper than the declared precision allows, and an admitted value
whose earliest completion falls below the universal Gregorian floor or the enabled pre-1900 boundary.
So calendar unreality is *not* grouped with the omission failures even though both reject a value the
declaration could otherwise hold.

A **full-precision** declaration is deliberately outside this classifier: it allows no omission at all,
and measured, it reports every omission marker as `dateFormat` rather than as an omission failure.
[`FullDateInput.lean`](FullDateInput.lean) owns that declaration and already reports exactly that.

The boundary is stored-text classification alone. An admitted partial value is **not** projected into
the shared cell value domain, because it denotes an interval rather than an instant and acquires a
`FullDate` only when `ValueAsDate` selects an endpoint; giving it a cell value here would have to
invent one of those endpoints. Wider format syntax, model-zone resolution, and addressing stay with
their existing owners. -/

namespace A12Kernel

/-- Fail-closed reasons before a declaration can use the bounded partial-Date input classifier. -/
inductive CanonicalPartialDateFieldError where
  | notDate (path : List String) (actual : FieldKind)
  | policyUnavailable (path : List String)
  /-- The declaration is a Date but allows no omission, so the full-precision classifier owns it. -/
  | fullPrecision (path : List String)
  | unsupportedPolicy (path : List String) (format : String)
      (partialMode : TemporalPartialMode)
  deriving Repr, DecidableEq

/-- One Date declaration whose kind, complete component shape, allowed omission precision, and input
format are model-owned. The precision is retained as its own field so a consumer reads the admitted
omission depth without re-deriving it from the policy. -/
structure CheckedPartialDateInputField where
  private mk ::
  declaration : FlatFieldDecl
  field : FlatTemporalField
  policy : TemporalTargetPolicy
  format : FullDateTargetFormat
  mode : TemporalPartialMode
  fieldOwned : declaration.toTemporalField? = some field
  policyOwned : declaration.toTemporalTargetPolicy? = some policy
  /-- Not an independent kind test: a partial mode **implies** a Date declaration. `datePrecision`
      is a field of the Kernel's `DateType` alone, `TimeType` and `DateTimeType` each declare only
      `format`, and hand-writing the property onto a `TimeType` is refused by the Kernel's own
      deserializer before any check runs. So the pairing this obligation would need in order to be
      wrong — a non-`full` precision on a non-Date kind — is not expressible in the model format,
      and this equality records a consequence of the precision requirement rather than a second gate
      ([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format)).
      That is why it stays while the ten measured kind conjuncts in this class went. -/
  kindOwned : field.kind = .date
  componentsOwned : field.components = TemporalComponents.fullDate
  modeOwned : policy.partialMode = mode
  admitsOmission : mode ≠ .full
  formatOwned : FullDateTargetFormat.ofSource? policy.format = some format

/-- Certify one bounded partial-Date input declaration without imposing an addressing shape. -/
def certifyPartialDateInputField (declaration : FlatFieldDecl) :
    Except CanonicalPartialDateFieldError CheckedPartialDateInputField :=
  match hField : declaration.toTemporalField? with
  | none => .error (.notDate declaration.path declaration.policy.kind)
  | some field =>
      if hKind : field.kind = .date then
        if hComponents : field.components = TemporalComponents.fullDate then
          match hPolicy : declaration.toTemporalTargetPolicy? with
          | none => .error (.policyUnavailable declaration.path)
          | some policy =>
              if hMode : policy.partialMode = .full then
                .error (.fullPrecision declaration.path)
              else
                match hFormat : FullDateTargetFormat.ofSource? policy.format with
                | none => .error (.unsupportedPolicy declaration.path
                    policy.format policy.partialMode)
                | some format => .ok {
                    declaration
                    field
                    policy
                    format
                    mode := policy.partialMode
                    fieldOwned := hField
                    policyOwned := hPolicy
                    kindOwned := hKind
                    componentsOwned := hComponents
                    modeOwned := rfl
                    admitsOmission := hMode
                    formatOwned := hFormat }
        else
          .error (.notDate declaration.path declaration.policy.kind)
      else
        .error (.notDate declaration.path declaration.policy.kind)

/-- Classify stored text of a certified partial-Date declaration, reading the deciding facts off its
certificate. -/
def CheckedPartialDateInputField.classifyStored
    (checked : CheckedPartialDateInputField) (text : String) :
    PartialDateInputCell checked.mode :=
  classifyPartialDateStored checked.format checked.mode
    checked.policy.youngerThan1900Check text

/-- Whether the declaration admits `text` as a **partially** known value, the one a cell places as
`Value.partialDate`; a fully known value places as a temporal value instead. -/
def CheckedPartialDateInputField.admitsPartiallyKnownText
    (checked : CheckedPartialDateInputField) (text : String) : Bool :=
  match checked.classifyStored text with
  | .admitted value =>
      match value.value with
      | .full _ => false
      | .omittedDay _ | .omittedMonth _ | .omittedYear => true
  | .presentEmpty | .rejected _ => false

end A12Kernel
