import A12Kernel.Elaboration.FullDateInput
import A12Kernel.Elaboration.TimeInput

/-! # Checked DateTime stored input

This bounded classifier owns a DateTime declaration at `yyyy-MM-dd'T'HH:mm:ss`, and its `'T'` is part
of that format rather than tolerated whitespace. Other vocabulary formats are authorable on a DateTime
field but remain outside this classifier. The admitted profile is classified into the `RawCell` the
checked document already carries, resolving the wall label in the model zone exactly as the full-Date
classifier does.

**Two causes, split the same way as every other temporal input in this project.** A spelling or range
question is `dateFormat`: a wrong separator or component width, an unreal calendar date in the date
half, and an out-of-range clock in the time half — hour `24` included. A position-in-time question is
`dateInvalid`: measured, a DateTime carries the **same** `1583-10-16` universal floor as a Date, so
`1583-10-15T00:00:00` is refused while `1583-10-16T00:00:00` is admitted.

Both halves are decided as spelling before the floor is consulted, which is the ordering the partial-Date
classifier measured for its own two causes; the interaction of a bad clock with a below-floor date is not
itself measured, so this order is inherited rather than separately established. The optional pre-1900
check cannot arise here, because the policy gate already refuses it on a DateTime declaration.

The date half's calendar reality and its `storedGregorian` provenance are the full-Date classifier's
account, reused rather than restated: the same component parser, the same legacy-hybrid reality test,
and the same stored basis. Wider formats, other zones, and repeatable addressing stay with their
existing owners. -/

namespace A12Kernel

/-- Fail-closed reasons before a declaration can use the bounded DateTime input classifier. -/
inductive CanonicalDateTimeFieldError where
  | notDateTime (path : List String) (actual : FieldKind)
  | policyUnavailable (path : List String)
  /-- The declaration is a DateTime whose format is not this classifier's storage format. Reachable rather than
  defensive: the model gate admits any vocabulary format on any temporal kind. -/
  | unsupportedFormat (path : List String) (format : String)
  deriving Repr, DecidableEq

/-- One DateTime declaration whose kind and storage format are model-owned. -/
structure CheckedDateTimeInputField where
  private mk ::
  declaration : FlatFieldDecl
  field : FlatTemporalField
  policy : TemporalTargetPolicy
  format : DateTimeTargetFormat
  fieldOwned : declaration.toTemporalField? = some field
  policyOwned : declaration.toTemporalTargetPolicy? = some policy
  kindOwned : field.kind = .dateTime
  formatOwned : DateTimeTargetFormat.ofSource? policy.format = some format

/-- Certify one bounded DateTime input declaration without imposing an addressing shape. -/
def certifyDateTimeInputField (declaration : FlatFieldDecl) :
    Except CanonicalDateTimeFieldError CheckedDateTimeInputField :=
  match hField : declaration.toTemporalField? with
  | none => .error (.notDateTime declaration.path declaration.policy.kind)
  | some field =>
      if hKind : field.kind = .dateTime then
        match hPolicy : declaration.toTemporalTargetPolicy? with
        | none => .error (.policyUnavailable declaration.path)
        | some policy =>
            match hFormat : DateTimeTargetFormat.ofSource? policy.format with
            | none =>
                .error (.unsupportedFormat declaration.path policy.format)
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
        .error (.notDateTime declaration.path declaration.policy.kind)

/-- The date half of the one DateTime storage format. Its spelling is the dashed full-Date format, so
the component parser and calendar-reality test are that classifier's rather than a second copy. -/
def DateTimeTargetFormat.dateHalf :
    DateTimeTargetFormat → FullDateTargetFormat
  | .yearMonthDayTime => .yearMonthDayDashes

/-- Split one stored DateTime label at the format's literal `T`. A space in that position is **not**
tolerated, which is measured, so this returns `none` for it exactly as for a missing separator. -/
def DateTimeTargetFormat.splitLabel? (_ : DateTimeTargetFormat)
    (text : String) : Option (String × String) :=
  match text.splitOn "T" with
  | [dateText, timeText] => some (dateText, timeText)
  | _ => none

/-- The bounded classifier cannot resolve a label outside its exact model-zone profile. A locally
impossible wall label stays distinct from a formal text failure, as it does for a full Date. -/
inductive DateTimeInputError where
  | unsupportedZone (zoneId : String)
  | unresolvableDateTime (parts : DateParts) (time : TimeOfDay)
  deriving Repr, DecidableEq

/-- Classify stored DateTime text under its certified declaration and one bounded model-zone profile.
Formal text failures are successful classifications; only unsupported or unresolvable model context
returns an error. -/
def CheckedDateTimeInputField.classifyStoredForModel
    (checked : CheckedDateTimeInputField) (zoneId text : String) :
    Except DateTimeInputError RawCell := do
  let profile ← match ModelZone.ConcreteProfile.ofId? zoneId with
    | some profile => pure profile
    | none => throw (.unsupportedZone zoneId)
  if text.isEmpty then
    pure .presentEmpty
  else
    match checked.format.splitLabel? text with
    | none => pure (.rejected .dateFormat)
    | some (dateText, timeText) =>
        -- Both halves are spelling questions and are settled first; only then does the date's position
        -- in time speak. A clock has no position of its own, which is why one floor test serves.
        match checked.format.dateHalf.parseLegacyParts? dateText,
            decodeTimeLiteral? timeText with
        | some parts, some clock =>
            if decide (parts.Before CivilDate.gregorianFloor.parts) then
              pure (.rejected .dateInvalid)
            else
              match CivilDate.ofParts? parts with
              | none => pure (.rejected .dateFormat)
              | some date =>
                  match FullDate.ofCivil? date with
                  | none => pure (.rejected .dateFormat)
                  | some full =>
                      match LocalDateTime.ofDateHms? full clock.hour clock.minute
                          clock.second with
                      | none => throw (.unresolvableDateTime parts clock)
                      | some wallLabel =>
                          match profile.resolveLocal? wallLabel with
                          | none => throw (.unresolvableDateTime parts clock)
                          | some instant =>
                              pure (.parsed (.temporal
                                (.dateTime instant date.parts clock
                                  .storedGregorian)))
        | _, _ => pure (.rejected .dateFormat)

end A12Kernel
