import A12Kernel.Elaboration.BooleanFirstFilledComputation
import A12Kernel.Elaboration.DateFragmentFirstFilledComputation
import A12Kernel.Elaboration.DateTimeFirstFilledComputation
import A12Kernel.Elaboration.DateTimeInput
import A12Kernel.Elaboration.FullDateFirstFilledComputation
import A12Kernel.Elaboration.FullDateInput
import A12Kernel.Elaboration.TimeFirstFilledComputation
import A12Kernel.Elaboration.TimeInput

/-! # Direct-list fixed-target `FirstFilledValue` locks

Every row of the
[four-carrier capture](../../docs/sources/evaluation-and-application-routes.md#src-first-filled-formal-branch-four-carriers),
replayed through each carrier's own check of a two-field direct list: `FirstFilledValue(B1, B2)` into a
Boolean, `(G1, G2)` into a `yyyy-MM` DateFragment, `(T1, T2)` into an `HH:mm:ss` Time and `(M1, M2)`
into an ISO DateTime, all fixed fields of the root `Fc` in zone `Europe/Berlin`; and every direct row
of the [malformed-prefix capture](../../docs/sources/evaluation-and-application-routes.md#src-first-filled-malformed-terminates-and-inventory-reports),
`FirstFilledValue(D1, D2)` into a `yyyy-MM-dd` Date, whose starred rows the full-Date star carrier owns. A row projects each
carrier's result to its stored text, or `-` where the Kernel clears a seeded target or reports no
outcome for an unseeded one; the two differ by prior target state alone, which the shared result
classifier owns, so a scan result only claims that it writes no value. The operand inventory's
`formalErrorsInOperands` is not replayed here.

The rows separate an empty first source, which falls through to the second, from a malformed one,
which ends the scan with the good second source unread; and a malformed second source behind a filled
first, which the scan never reaches.
-/

namespace A12Kernel.Conformance.FirstFilledFieldList

open A12Kernel

private def field (id : FieldId) (name : String) (kind : FieldKind)
    (policy : Option TemporalTargetPolicy := none) : FlatFieldDecl :=
  { id, groupPath := ["Fc"], name, policy := { kind }, temporalTargetPolicy := policy }

private def boolean (id : FieldId) (name : String) := field id name .boolean

private def fragment (id : FieldId) (name : String) :=
  field id name (.temporal .date (TemporalComponents.ofFormat "yyyy-MM")) (some { format := "yyyy-MM" })

private def clock (id : FieldId) (name : String) :=
  field id name (.temporal .time TemporalComponents.time) (some { format := "HH:mm:ss" })

private def moment (id : FieldId) (name : String) :=
  field id name (.temporal .dateTime TemporalComponents.now)
    (some { format := "yyyy-MM-dd'T'HH:mm:ss", partialMode := .full })

private def date (id : FieldId) (name : String) :=
  field id name (.temporal .date TemporalComponents.fullDate)
    (some { format := "yyyy-MM-dd", partialMode := .full })

private def range (id : FieldId) (name : String) : FlatFieldDecl :=
  { field id name .dateRange with dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }

private def model : FlatModel :=
  { fields := [
      boolean 0 "B1", boolean 1 "B2", boolean 2 "BTgt",
      fragment 3 "G1", fragment 4 "G2", fragment 5 "GTgt",
      clock 6 "T1", clock 7 "T2", clock 8 "TTgt",
      moment 9 "M1", moment 10 "M2", moment 11 "MTgt",
      date 12 "D1", date 13 "D2", date 14 "DTgt",
      boolean 15 "B3", { boolean 16 "RB" with groupPath := ["Fc", "Rows"], repeatableScope := [10] },
      { date 17 "DD" with temporalTargetPolicy := some { format := "dd.MM.yyyy", partialMode := .full } },
      range 18 "R1", range 19 "R2", range 20 "RTgt"]
    repeatableGroups := [{ level := 10, path := ["Fc", "Rows"], repeatability := some 3 }]
    timeZoneId := "Europe/Berlin" }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler
    model).toOption.get (by native_decide)

private def operand (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field := name }

private def list (names : List String) : SurfaceFirstFilledSource :=
  match names with
  | first :: rest => .list { first := operand first, rest := rest.map operand }
  | [] => .list { first := operand "", rest := [] }

/-- One fragment cell as the DateFragment conformance builds it: the stored token beside a parsed
date of that year and month, or the format rejection for a text that is no `yyyy-MM`. -/
private def fragmentRaw (text : String) : RawCell :=
  match text.splitOn "-" with
  | [year, month] =>
      match year.toNat?, month.toNat? with
      | some year, some month =>
          .parsed (.temporal (.date {
            instant := { epochMillis := 0 }
            parts := { year := year, month := month, day := 1 }
            basis := .storedGregorian }))
      | _, _ => .rejected .dateFormat
  | _ => .rejected .dateFormat

private def raw (declaration : FlatFieldDecl) (text : String) : RawCell :=
  match declaration.policy.kind with
  | .boolean => classifyStoredBooleanText text
  | .temporal .time _ =>
      match certifyTimeInputField declaration with
      | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD
          (.rejected .dateFormat)
      | .error _ => .rejected .dateFormat
  | .temporal .dateTime _ =>
      match certifyDateTimeInputField declaration with
      | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD
          (.rejected .dateFormat)
      | .error _ => .rejected .dateFormat
  | .temporal .date _ =>
      if declaration.toTemporalTargetPolicy?.map (·.format) == some "yyyy-MM-dd" then
        match certifyFullDateInputField declaration with
        | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD
            (.rejected .dateFormat)
        | .error _ => .rejected .dateFormat
      else fragmentRaw text
  | _ => fragmentRaw text

/-- A document from `(field name, stored text)` pairs; an omitted field is absent. -/
private def input? (cells : List (String × String)) : Option (CheckedDocument model) := do
  let classified ← cells.mapM fun (name, text) => do
    let declaration ← model.fields.find? (·.name == name)
    pure { address := { field := declaration.id, path := [] }, stored := text
           raw := raw declaration text : ClassifiedCellInput }
  (checkDocument prepared "en_US" { instantiatedRows := [], cells := classified }).toOption

/-- The four carriers' results over one document, in the order `BTgt`, `GTgt`, `TTgt`, `MTgt`. -/
private def results? (cells : List (String × String)) : Option (List String) := do
  let input ← input? cells
  let booleanResult ← (checkBooleanFirstFilledComputation model ["Fc"] 2 (list ["B1", "B2"])).toOption
  let fragmentResult ←
    (checkDateFragmentFirstFilledComputation model ["Fc"] 5 (list ["G1", "G2"])).toOption
  let clockResult ← (checkTimeFirstFilledComputation model ["Fc"] 8 (list ["T1", "T2"])).toOption
  let momentResult ←
    (checkDateTimeFirstFilledComputation model ["Fc"] 11 (list ["M1", "M2"])).toOption
  let b ← (booleanResult.execute input).toOption
  let [{ result := g, .. }] ← (fragmentResult.execute input).toOption | none
  let [{ outcome := t, .. }] ← (clockResult.execute input).toOption | none
  let m ← (momentResult.execute input).toOption
  pure [
    match b with | .value value => toString value | _ => "-",
    match g with | .value token => token | _ => "-",
    match t with | .accepted stored => stored.text | _ => "-",
    match m with | .accepted stored => stored.text | _ => "-"]

private def firsts (b g t m : String) : List (String × String) :=
  [("B1", b), ("G1", g), ("T1", t), ("M1", m)]

private def seconds (b g t m : String) : List (String × String) :=
  [("B2", b), ("G2", g), ("T2", t), ("M2", m)]

private def good₁ := firsts "true" "2026-05" "08:30:00" "2026-05-04T08:30:00"
private def good₂ := seconds "false" "2026-07" "09:45:00" "2026-07-08T09:45:00"
private def bad₁ := firsts "maybe" "nonsense" "99:99:99" "nonsense"
private def bad₂ := seconds "maybe" "nonsense" "99:99:99" "nonsense"

/- Rows `c-first-empty-second-good` and `q-first-malformed` with its seeded twin: an empty first source
falls through to the second, while a malformed one ends the scan and the good second goes unread. -/
example :
    results? good₂ = some ["false", "2026-07", "09:45:00", "2026-07-08T09:45:00"] ∧
    results? (bad₁ ++ good₂) = some ["-", "-", "-", "-"] := by
  native_decide

/- Rows `c-both-empty-stale`, `q-second-malformed` and `q-empty-then-malformed`: exhaustion writes no
value, a filled first source is selected before the malformed second is reached, and a malformed
second behind an empty first ends the scan. -/
example :
    results? [] = some ["-", "-", "-", "-"] ∧
    results? (good₁ ++ bad₂) = some ["true", "2026-05", "08:30:00", "2026-05-04T08:30:00"] ∧
    results? bad₂ = some ["-", "-", "-", "-"] := by
  native_decide

/-- The full-Date carrier's result over one document. -/
private def dateResult? (cells : List (String × String)) : Option String := do
  let input ← input? cells
  let operation ←
    (checkFullDateFirstFilledComputation model ["Fc"] 14 (list ["D1", "D2"])).toOption
  match ← (operation.execute input).toOption with
  | .accepted stored => pure stored.text
  | _ => pure "-"

/- The malformed-prefix capture's direct rows `c1` to `c3` and `q1` to `q4`, in that order; its seeded
twins `c4`, `q5` and `q6` differ only in prior target state. -/
example :
    [[("D1", "2026-01-01"), ("D2", "2026-02-02")], [("D2", "2026-02-02")], [],
      [("D1", "nonsense"), ("D2", "2026-02-02")], [("D1", "2026-01-01"), ("D2", "nonsense")],
      [("D1", "nonsense")], [("D2", "nonsense")]].map dateResult? =
      [some "2026-01-01", some "2026-02-02", some "-", some "-", some "2026-01-01", some "-",
        some "-"] := by
  native_decide

private def entries (operands : List SurfaceFieldEntityOperand) : SurfaceFirstFilledSource :=
  match operands with
  | first :: rest => .list { first, rest }
  | [] => .list { first := operand "", rest := [] }

private def booleanError? (operands : List SurfaceFieldEntityOperand) :
    Option BooleanFirstFilledComputationElabError :=
  match checkBooleanFirstFilledComputation model ["Fc"] 2 (entries operands) with
  | .ok _ => none
  | .error cause => some cause

private def rowsStar : SurfaceFieldEntityOperand :=
  .star { base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "RB" }

/- The list's representation boundary, each refusal at the layer that owns it and none claiming a
Kernel class: three fields are admitted, a sole direct field fails the entity list's arity, a star
operand is no plain field, a list naming its own target and a list mixing kinds are refused by the
carrier, and a field under a repeatable group fails the shared shape as an unbound level. -/
example :
    ((booleanError? [operand "B1", operand "B2", operand "B3"]).isNone &&
      (match booleanError? [operand "B1"] with
        | some (.list (.shape .tooFewFields)) => true | _ => false) &&
      (match booleanError? [operand "B1", rowsStar] with
        | some (.list .unsupportedOperand) => true | _ => false) &&
      (match booleanError? [operand "B1", operand "BTgt"] with
        | some (.targetSelfReference path) => path == ["Fc", "BTgt"] | _ => false) &&
      (match booleanError? [operand "B1", operand "T1"] with
        | some (.sourceKind path _) => path == ["Fc", "T1"] | _ => false) &&
      (match booleanError?
          [operand "B1", .field { base := .relative 0, groups := ["Rows"], field := "RB" }] with
        | some (.list (.shape (.resolve (.unboundOperandLevel _ _)))) => true | _ => false)) =
      true := by
  native_decide

/- Every listed field repeats one carrier profile: two full Dates spelled differently, which the Kernel
refuses `MVK_VARYING_TYPES_NOT_ALLOWED`, two kinds, and an ISO list into a dotted target, whose
Kernel treatment is unmeasured, are each refused here as a profile mismatch; and the shared shape
refuses a list over a DateRange profile, which the direct DateRange carrier owns. -/
example :
    ((match checkFullDateFirstFilledComputation model ["Fc"] 14 (list ["D1", "DD"]) with
        | .error (.shape (.sourceCarrier path)) => path == ["Fc", "DD"] | _ => false) &&
      (match checkTimeFirstFilledComputation model ["Fc"] 8 (list ["T1", "M1"]) with
        | .error (.shape (.sourceCarrier path)) => path == ["Fc", "M1"] | _ => false) &&
      (match checkFullDateFirstFilledComputation model ["Fc"] 17 (list ["D1", "D2"]) with
        | .error (.shape (.sourceCarrier path)) => path == ["Fc", "D1"] | _ => false) &&
      (match checkTemporalFirstFilledShape model ["Fc"] 20 (list ["R1", "R2"]) .dateRangeIsoSlash with
        | .error (.sourceShape path) => path == ["Fc", "RTgt"] | _ => false)) = true := by
  native_decide

end A12Kernel.Conformance.FirstFilledFieldList
