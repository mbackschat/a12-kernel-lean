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
    (groupPath : GroupPath := ["Probe"])
    (repeatableScope : List RepeatableLevel := []) : FlatFieldDecl :=
  { id, groupPath, name, repeatableScope,
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
      policy := { kind := .string } },
    { id := 13, groupPath := ["Probe"], name := "Amount",
      policy := { kind := .number { scale := 0, signed := false } } },
    { id := 14, groupPath := ["Probe"], name := "Flag",
      policy := { kind := .boolean } },
    -- Enumeration stands for the three kinds still unmeasured at this gate; the point of its row is
    -- the absent class, so any one of them serves and a second adds nothing.
    { id := 15, groupPath := ["Probe"], name := "Choice",
      policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["a", "b"] } }]

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

/-- A repeatable row carrying a full-date field and a numeric guard, plus a **non**-repeatable `Sub`
    beneath it. `Sub` is what makes the starred-group *presence* form reachable from the surface:
    a starred group resolves to the presence source exactly when its terminal is not itself a
    repeatable level, so without a nested nonrepeatable group the declined arm could not be
    exercised at all. -/
private def rowDeclarations : List FlatFieldDecl :=
  [ temporal 30 "RowDate" .date (dateParts true true true) "yyyy-MM-dd"
      (groupPath := ["Probe", "Rows"]) (repeatableScope := [10]),
    { id := 31, groupPath := ["Probe", "Rows"], name := "RowVal",
      repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := false } } },
    temporal 32 "SubDate" .date (dateParts true true true) "yyyy-MM-dd"
      (groupPath := ["Probe", "Rows", "Sub"]) (repeatableScope := [10]) ]

private def starModel : FlatModel :=
  { fields := declarations ++ groupDeclarations ++ rowDeclarations
    repeatableGroups :=
      [{ level := 10, path := ["Probe", "Rows"], repeatability := some 3 }] }

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

/-! ## The family gate, which is positional

The first operand chooses the family, so the *same pair* draws different codes in the two orders.
Temporal first with a non-temporal after it is the Kernel's own `MVK_DATE_AND_NONDATE`; non-temporal
first means the list was never this family's, and the Number entity list draws `MVK_NOT_SORTABLE`
there — so this module claims nothing in that order. Both orders of both pairs are locked, because
one order alone leaves a kind-keyed account standing, which is what this module carried until the
gate was measured. -/

private def number : FieldId := 13

example : refusal? plainModel [1, 12] = some .dateAndNonDate := by native_decide

example : refusal? plainModel [1, number] = some .dateAndNonDate := by native_decide

/- Reversed, and the class disappears rather than changing: a non-temporal first operand is the
   Number list's business, and this list reporting a code there would be the false-class defect. -/
example : refusal? plainModel [12, 1] = none := by native_decide

example : refusal? plainModel [number, 1] = none := by native_decide

/- Neither order is admitted; only the reported class differs. -/
example : admitted plainModel [1, 12] = false := by native_decide

example : admitted plainModel [12, 1] = false := by native_decide

/- Position and not arity: the offending operand is third here and still draws the later-operand
   class, so "later" means "not first" rather than "second". -/
example : refusal? plainModel [1, 2, 12] = some .dateAndNonDate := by native_decide

/- Boolean in later position draws the same class, measured
   ([checkpoint](../../docs/SOURCES.md#src-later-position-kinds-and-group-expansion-class)), and
   `MinValue` agrees with `MaxValue` on it. Three kinds now share this class from three separate
   families, which is what makes the Kernel's generalizing message text — *"if the first parameter is
   a date than all parameters have to be dates"* — look like a rule rather than one pair's accident.
   It is still text and not a row, so the three kinds below it stay unprojected. -/
example : refusal? plainModel [1, 14] = some .dateAndNonDate := by native_decide

example : admitted plainModel [1, 14] = false := by native_decide

/- **Every** kind draws it. Enumeration, Confirm and DATE_RANGE were the last three unmeasured, and
   all three landed on this class beside a Boolean control on the same model
   ([checkpoint](../../docs/SOURCES.md#src-later-position-class-is-total-and-presence-is-admitted)),
   so the gate is now total in the later position rather than a set of measured kinds. Enumeration
   stands for the three here because the projection no longer branches on kind at all — which is the
   point: a row per kind would test the same constant. -/
private def enumeration : FieldId := 15

example : refusal? plainModel [1, enumeration] = some .dateAndNonDate := by
  native_decide

example : admitted plainModel [1, enumeration] = false := by native_decide

/-! ## A filtered star is an operand like any other

The gate reads the declaration a `Having`-filtered star names, exactly as it reads a plain star's.
The filter selects **rows**, so it cannot change the component set of the field being read, and the
measured rows say the Kernel agrees: a filtered star is admitted wherever the plain star is, and
draws the same incompatibility against a differing set
([checkpoint](../../docs/SOURCES.md#src-filtered-star-temporal-carriers-and-binding-depth)).

This capsule previously declined the form, on the stated ground that the neighbouring DateRange
carrier refuses starred operands outright and reading admission across that boundary would be the
crossing [`LF116`](../../docs/LEAN-FINDINGS.md) warns about. The decline was correct to demand a
measurement and wrong about the answer. -/

private def rowDateStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Probe" }, { name := "Rows", starred := true }]
    field := "RowDate" }

/-- A filter over the row's own guard. Its content is immaterial to the component gate — what the
    rows below test is that a filter is *present* without changing the verdict — so the cheapest
    well-formed one serves. -/
private def rowFilter : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner,
      field := { base := .absolute, groups := ["Probe", "Rows"], field := "RowVal" } }
    { origin := .inner,
      field := { base := .absolute, groups := ["Probe", "Rows"], field := "RowVal" } }

private def plainStarOperand : SurfaceFieldEntityOperand := .star rowDateStar

private def filteredStarOperand : SurfaceFieldEntityOperand :=
  .starHaving rowDateStar rowFilter

/- The two star forms are admitted alone, and the filtered one carries the same lifted set as the
   plain one — the property that makes the pair below a comparison rather than two readings. -/
example :
    groupAdmitted starModel [plainStarOperand] = true ∧
      groupAdmitted starModel [filteredStarOperand] = true := by
  native_decide

example :
    (elaborateAt starModel [filteredStarOperand]).toOption.map (·.components) =
      (elaborateAt starModel [plainStarOperand]).toOption.map (·.components) := by
  native_decide

/- Beside a matching set, and beside the **other spelling** of that set: admitted both times. The
   second is the row that keeps this from reading as a format-string gate, and it is the one the
   Kernel confirmed directly. -/
example :
    groupAdmitted starModel [filteredStarOperand, operandOf 1] = true ∧
      groupAdmitted starModel [filteredStarOperand, operandOf 2] = true := by
  native_decide

/- Beside a **differing** set, refused — so admission above is the gate passing, not the gate being
   skipped for filtered operands. Paired with the plain star on the identical list, because the
   claim is that the filter changes nothing and a single row cannot say that. -/
example :
    groupRefusal? starModel [filteredStarOperand, operandOf 3] =
        some .dateFormatsNotCompatible ∧
      groupRefusal? starModel [plainStarOperand, operandOf 3] =
        some .dateFormatsNotCompatible := by
  native_decide

/- And in a later position the filtered star is still read, drawing the same class when it disagrees
   with a first operand that fixed a different set. -/
example :
    groupRefusal? starModel [operandOf 3, filteredStarOperand] =
      some .dateFormatsNotCompatible := by
  native_decide

/-! ## A starred group whose terminal is nonrepeatable

The **presence** form — a star above a group that is not itself a repeatable level — is admitted,
and its component gate reads the expansion exactly as a starred repeatable group's does
([checkpoint](../../docs/SOURCES.md#src-later-position-class-is-total-and-presence-is-admitted)).
The measured control that makes this a property of the *star* rather than of the group is the same
path read **without** one, which draws `MVK_NO_WILDCARD`.

The rows below need a homogeneous temporal expansion under `Sub`, which is also the trap the
measurement walked into: adding a date beside the existing Number made the expansion *mixed*, and
the row then measured the mixed-expansion rule a second time instead of the form. -/
private def presenceGroup : SurfaceFieldEntityOperand :=
  .starredGroup
    { base := .absolute
      groups := [{ name := "Probe" }, { name := "Rows", starred := true },
        { name := "Sub" }] }

example : groupAdmitted starModel [presenceGroup] = true := by native_decide

/- The gate reads its expansion: a differing set refuses, and the same set spelled otherwise is
   admitted. Without the refusal row, admission alone is equally well explained by the form skipping
   the gate — which would be a worse outcome than a refusal, since it would let a group operand
   smuggle an incompatible declaration past it. -/
example :
    groupRefusal? starModel [presenceGroup, operandOf 3] =
        some .dateFormatsNotCompatible ∧
      groupAdmitted starModel [presenceGroup, operandOf 2] = true := by
  native_decide

/- And its expansion fixes the leading class, so a non-temporal later operand draws the date class
   rather than none — the presence form participates in the positional rule like any other. -/
example :
    groupRefusal? starModel [presenceGroup, operandOf 12] = some .dateAndNonDate := by
  native_decide

end A12Kernel.Conformance.TemporalExtremumOperands
