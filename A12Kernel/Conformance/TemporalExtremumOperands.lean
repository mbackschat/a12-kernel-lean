import A12Kernel.Elaboration.TemporalExtremumOperands
import A12Kernel.Semantics.TemporalFormat

/-! # A12Kernel.Conformance.TemporalExtremumOperands — the extrema's temporal operand gate

Three readings of this gate predict different verdicts, and the rows below are chosen to keep only
one alive. It is **not** the declared format string: two spellings of one component set cross it.
It is **not** the declared kind: a TIME and a DATE_TIME are admitted together at one shared set.
(The measured DATE-beside-DATE_FRAGMENT pair cannot say that here, because this model represents a
fragment as a DATE with a partial set; the body says so where the row sits.) It is the **component set**, with a declared Base Year supplying a missing year
before the comparison — and the year-only operand is the row that stops that lifting from reading as
"a Base Year makes any two date operands compatible".

The sibling `FieldValuesNotUnique` carrier really does gate on the format string, so the
same-set-different-spelling rows are exactly where the two carriers part.
-/

namespace A12Kernel.Conformance.TemporalExtremumOperands

open A12Kernel

private def dateParts (year month day : Bool) : TemporalComponents :=
  { year, month, day, hour := false, minute := false, second := false }

private def temporal (id : Nat) (name : String) (kind : TemporalKind)
    (components : TemporalComponents) (format : String)
    (groupPath : GroupPath := ["Probe"]) : FlatFieldDecl :=
  { id, groupPath, name,
    policy := { kind := .temporal kind components },
    temporalTargetPolicy := some { format } }

/-- One declaration per spelling the matrix needs, plus a String control. Ids are stable across the
    two models so a row can be read against both Base Year states. -/
private def declarations : List FlatFieldDecl :=
  [ temporal 1 "IsoDate" .date (dateParts true true true) "yyyy-MM-dd",
    temporal 2 "DottedDate" .date (dateParts true true true) "dd.MM.yyyy",
    temporal 3 "IsoYearMonth" .date (dateParts true true false) "yyyy-MM",
    temporal 4 "PackedYearMonth" .date (dateParts true true false) "yyyyMM",
    temporal 5 "DateYear" .date (dateParts true false false) "yyyy",
    temporal 6 "FragmentYear" .date (dateParts true false false) "yyyy",
    temporal 7 "Clock" .time TemporalComponents.time "HH:mm:ss",
    temporal 8 "StampAsClock" .dateTime TemporalComponents.time "HH:mm:ss",
    temporal 9 "Stamp" .dateTime TemporalComponents.now "yyyy-MM-dd HH:mm:ss",
    temporal 10 "MonthOnly" .date (dateParts false true false) "MM",
    temporal 11 "MonthDay" .date (dateParts false true true) "MM-dd",
    { id := 12, groupPath := ["Probe"], name := "Text",
      policy := { kind := .string } }]

/-- Two group slots whose expansions differ in exactly the thing under test. -/
private def groupDeclarations : List FlatFieldDecl :=
  [ temporal 20 "SameA" .date (dateParts true true true) "yyyy-MM-dd"
      (groupPath := ["Probe", "Same"]),
    temporal 21 "SameB" .date (dateParts true true true) "dd.MM.yyyy"
      (groupPath := ["Probe", "Same"]),
    temporal 22 "MixedA" .date (dateParts true true true) "yyyy-MM-dd"
      (groupPath := ["Probe", "Mixed"]),
    temporal 23 "MixedB" .date (dateParts true false false) "yyyy"
      (groupPath := ["Probe", "Mixed"]) ]

private def plainModel : FlatModel :=
  { fields := declarations ++ groupDeclarations }

private def baseYearModel : FlatModel :=
  { fields := declarations ++ groupDeclarations, baseYear := some 2024 }

private def fieldOperand (groups : GroupPath) (name : String) :
    SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups, field := name }

private def operandOf (source : FieldId) : SurfaceFieldEntityOperand :=
  match (declarations ++ groupDeclarations).find? (·.id == source) with
  | some declaration => fieldOperand declaration.groupPath declaration.name
  | none => fieldOperand ["Probe"] "?"

private def groupOperand (groups : GroupPath) : SurfaceFieldEntityOperand :=
  .group (.path { base := .absolute, groups })

private def sourceOf : List SurfaceFieldEntityOperand → SurfaceFieldEntitySource
  | [] => { first := groupOperand ["Probe"], rest := [] }
  | first :: rest => { first, rest }

private def elaborateAt (model : FlatModel)
    (operands : List SurfaceFieldEntityOperand) :=
  TemporalExtremumOperands.elaborate model ["Probe"] (sourceOf operands)

private def admitted (model : FlatModel) (sources : List FieldId) : Bool :=
  (elaborateAt model (sources.map operandOf)).toOption.isSome

private def refusal? (model : FlatModel) (sources : List FieldId) :
    Option KernelStaticDiagnostic :=
  match elaborateAt model (sources.map operandOf) with
  | .ok _ => none
  | .error error => error.diagnostic?

private def groupAdmitted (model : FlatModel)
    (operands : List SurfaceFieldEntityOperand) : Bool :=
  (elaborateAt model operands).toOption.isSome

private def groupRefusal? (model : FlatModel)
    (operands : List SurfaceFieldEntityOperand) : Option KernelStaticDiagnostic :=
  match elaborateAt model operands with
  | .ok _ => none
  | .error error => error.diagnostic?

/- Both fixtures are legal models, so no row below passes because the model failed to load. -/
example : plainModel.validate.isOk = true := by native_decide

example : baseYearModel.validate.isOk = true := by native_decide

/-! ## Not the format string

Same component set, two declared spellings, admitted — at full-date precision and again at
year-month, so the row is not one format pair's accident. -/

example : admitted plainModel [1, 2] = true := by native_decide

example : admitted plainModel [3, 4] = true := by native_decide

/-! ## Not the declared kind

The measured DATE-beside-DATE_FRAGMENT pair is **agreement by construction** here: this model has
three temporal kinds and a date fragment is a DATE with a partial component set, so the two sides of
that pair are one declaration shape and no row could separate them. The pair that does separate kind
from component set is a TIME beside a DATE_TIME declared with the degenerate time-only format — two
genuinely different kinds at one set — and it is also the witness spec prefers, because it does not
invite the objection that a fragment simply *is* a partial date. -/

example : admitted plainModel [5, 6] = true := by native_decide

example : admitted plainModel [7, 8] = true := by native_decide

/-! ## The component set, and its own refusal class

Two DATE_TIME declarations at genuinely different sets are refused, as is a complete date beside a
year-only one. -/

example : refusal? plainModel [8, 9] = some .dateFormatsNotCompatible := by
  native_decide

example : refusal? plainModel [1, 5] = some .dateFormatsNotCompatible := by
  native_decide

/-! ## A declared Base Year supplies the missing year, and only that

`MM` reaches `yyyy-MM` and `MM-dd` reaches a complete date once the year is supplied. Both stay
refused against the **year-only** operand, which is what separates "the Base Year completes a
yearless set" from "the Base Year makes date operands compatible". -/

example : admitted baseYearModel [10, 3] = true := by native_decide

example : admitted baseYearModel [11, 1] = true := by native_decide

example : refusal? baseYearModel [10, 5] = some .dateFormatsNotCompatible := by
  native_decide

example : refusal? baseYearModel [11, 5] = some .dateFormatsNotCompatible := by
  native_decide

/- Without the Base Year the same yearless pairs are refused, which is the control that makes the
   four rows above about the declaration and not about the component sets alone. -/
example : refusal? plainModel [10, 3] = some .dateFormatsNotCompatible := by
  native_decide

example : refusal? plainModel [11, 1] = some .dateFormatsNotCompatible := by
  native_decide

/-! ## Order does not change the admitted set

The first operand fixes the expected set, so a refusal names a path that depends on the authored
order — but which lists are admitted does not. -/

example : admitted plainModel [2, 1] = true := by native_decide

example : refusal? plainModel [5, 1] = some .dateFormatsNotCompatible := by
  native_decide

/-! ## Group slots, and the shared checker underneath

Structure is the shared entity-list checker's, so a group operand is a complete list by itself while
a lone fixed field is not — and the component gate then reads the group's **expansion** rather than
the group, which is the only way a heterogeneous subtree can be refused at all. -/

example : groupAdmitted plainModel [groupOperand ["Probe", "Same"]] = true := by
  native_decide

example : groupRefusal? plainModel [groupOperand ["Probe", "Mixed"]] =
    some .dateFormatsNotCompatible := by
  native_decide

/- A group beside a field of the same set is admitted, so the expansion joins the list rather than
   being checked in isolation. -/
example : groupAdmitted plainModel
    [groupOperand ["Probe", "Same"], operandOf 1] = true := by
  native_decide

/- The shared arity gate is live underneath: one fixed field is not a list, and its class is the
   shared checker's rather than this carrier's. -/
example : groupRefusal? plainModel [operandOf 1] = some .paramSizeInvalidN := by
  native_decide

/-! ## Outside this family, with nothing claimed

A String operand is refused here because this list is temporal, not because the Kernel was observed
refusing it at this position — the extrema admit Number operands, which the Number entity list owns.
The arm therefore projects no class. -/

example : admitted plainModel [1, 12] = false := by native_decide

example : refusal? plainModel [1, 12] = none := by native_decide

end A12Kernel.Conformance.TemporalExtremumOperands
