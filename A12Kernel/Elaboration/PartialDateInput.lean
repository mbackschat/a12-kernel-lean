import A12Kernel.Elaboration.FullDateInput
import A12Kernel.Semantics.PartialDate

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

/-- One classified stored cell of a partial-Date declaration. The admitted case carries its precision
witness, so a consumer cannot pair a value with a declaration that does not allow it. -/
inductive PartialDateInputCell (mode : TemporalPartialMode) where
  | presentEmpty
  | rejected (cause : FormalCause)
  | admitted (value : AdmittedPartiallyKnownDate mode)
  deriving Repr

/-- Classify stored text of a certified partial-Date declaration. Every formal text failure is a
successful classification carrying its cause; this classifier consults no model zone, because an
admitted partial value denotes an interval and resolves to an instant only under `ValueAsDate`. -/
def CheckedPartialDateInputField.classifyStored
    (checked : CheckedPartialDateInputField) (text : String) :
    PartialDateInputCell checked.mode :=
  if text.isEmpty then
    .presentEmpty
  else
    match checked.format.parseComponents? text with
    | none => .rejected .dateFormat
    | some parts =>
        -- The gates run in the measured order, and the order is the whole content of this clause:
        -- the *reality* of the present components is a calendar question decided first, its
        -- *position in time* is decided next, and only then does the declaration's precision judge
        -- the omission depth. Running the floor before reality would report an impossible month
        -- beside an omitted day as an omission failure, which the kernel does not.
        if parts.day = 0 && parts.month = 0 && parts.year = 0 then
          -- Nothing is present, so there is no calendar and no position to judge.
          gateByPrecision .omittedYear
        else if parts.day = 0 && parts.month = 0 then
          guardCompletion { year := parts.year, month := 1, day := 1 }
            (OmittedMonthDate.ofYear? (parts.year : Int) |>.map .omittedMonth)
        else if parts.day = 0 then
          guardCompletion { year := parts.year, month := parts.month, day := 1 }
            (OmittedDayDate.ofYearMonth? (parts.year : Int) parts.month
              |>.map .omittedDay)
        else if parts.month = 0 || parts.year = 0 then
          -- A present day beside an omitted month, or a present month or day beside an omitted year:
          -- the zeros are not a monotone suffix, so this is an omission failure, not a spelling one.
          .rejected .dateInvalid
        else
          guardCompletion parts
            (FullDate.ofYmd? (parts.year : Int) parts.month parts.day |>.map .full)
where
  /-- Apply the declaration's precision gate to one structurally legal shape. -/
  gateByPrecision (value : PartiallyKnownDateValue) : PartialDateInputCell checked.mode :=
    if h : checked.mode.admitsPartiallyKnownValue value = true then
      .admitted { value, admitted := h }
    else
      .rejected .dateInvalid
  /-- Judge one shape's earliest completion, then its precision. `earliest` is that completion's
  components and `build` the value it denotes. An unreal completion is a calendar failure; one below
  the universal floor, or below the enabled pre-1900 boundary, is a position-in-time failure. The
  builders apply the floor internally too, so `build` is consulted only after the floor has already
  passed and its `none` can mean nothing but unreality. -/
  guardCompletion (earliest : DateParts)
      (build : Option PartiallyKnownDateValue) : PartialDateInputCell checked.mode :=
    if !DateParts.LegacyHybrid.isReal earliest then
      .rejected .dateFormat
    else if decide (earliest.Before CivilDate.gregorianFloor.parts) ||
        (checked.policy.youngerThan1900Check &&
          decide (earliest.Before FullDate.year1900Start.civil.parts)) then
      .rejected .dateInvalid
    else
      match build with
      | none => .rejected .dateFormat
      | some value => gateByPrecision value

end A12Kernel
