import A12Kernel.Elaboration.ScalarComputationRunResult
import A12Kernel.Elaboration.PartialDateInput
import A12Kernel.Semantics.FieldFillQuantifier
import A12Kernel.Semantics.Required
import A12Kernel.Elaboration.TemporalValuesNotUnique

/-! # Presence of a partially known Date

Every row of the [presence grid](../../docs/sources/temporal-and-message-probes.md#src-partial-date-presence):
a `yyyy-MM-dd` Date at `DAY_OPTIONAL` (`PD`) and at `YEAR_OPTIONAL` (`PY`), a component-omitting
`yyyy-MM` Date (`FY`) and a `yyyy-MM` DateFragment (`GF`), each read by `FieldFilled`, `FieldNotFilled`
and one `NumberOfFilledFields` over all four. The Kernel answers both arms alike, so a row locks each
field's presence on both arms and the count.

The rows separate a partially known value, which is filled, from an empty cell, which is not, and both
from a value deeper than its precision admits, which is a formal failure reached by both presence tests
and by the count. A model reading a partially known value as present-empty, the encoding a stored text
with no value would give, answers the first row with `PD` and `PY` unfilled and a count of two.

The readers that consume the same presence are locked from the
[reader grid](../../docs/sources/temporal-and-message-probes.md#src-partial-date-readers): requiredness,
group content, which the once rule's root gate reads too, and `FieldValuesNotUnique`, which compares the
stored text rather than the date it completes to.
-/

namespace A12Kernel.Conformance.PartialDatePresence

open A12Kernel

private def date (id : FieldId) (name format : String) (mode : TemporalPartialMode) : FlatFieldDecl :=
  { id, groupPath := ["Pr"], name
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format, partialMode := mode } }

private def pd := date 0 "PD" "yyyy-MM-dd" .dayOptional
private def py := date 1 "PY" "yyyy-MM-dd" .yearOptional
private def fy := date 2 "FY" "yyyy-MM" .full
private def gf := date 3 "GF" "yyyy-MM" .yearOptional
private def pe := date 4 "PE" "yyyy-MM-dd" .dayOptional

private def model : FlatModel := { fields := [pd, py, fy, gf, pe] }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get (by native_decide)

private def dateValue (year month day : Nat) : RawCell :=
  .parsed (.temporal (.date {
    instant := { epochMillis := 0 }
    parts := { year := (year : Int), month := month, day := day }
    basis := .storedGregorian }))

/-- A precision-partial cell as the partial-Date classifier decides it: an admitted partially known
value, a fully known one, or the classifier's own rejection. -/
private def partialRaw (declaration : FlatFieldDecl) (text : String) : RawCell :=
  match certifyPartialDateInputField declaration with
  | .error _ => .rejected .dateFormat
  | .ok checked =>
      match checked.classifyStored text with
      | .presentEmpty => .presentEmpty
      | .rejected cause => .rejected cause
      | .admitted value =>
          match value.value with
          | .full date => dateValue date.civil.parts.year.toNat date.civil.parts.month
              date.civil.parts.day
          | _ => .parsed (.partialDate text)

private def cell (declaration : FlatFieldDecl) (text : String) (raw : RawCell) :
    ClassifiedCellInput :=
  { address := { field := declaration.id, path := [] }, stored := text, raw }

private def document? (cells : List ClassifiedCellInput) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption

private def flatField (declaration : FlatFieldDecl) : Option FlatField :=
  declaration.toTemporalField?.map .temporal

/-- Each field's `FieldFilled` and `FieldNotFilled` verdict, `1` for holds, `-` for not and `P` for
poison, and the four fields' filled count, `-` when unavailable. The verdicts are the computation
arm's, and the validation arm's must agree with them, `unknown` standing for poison. -/
private def answers? (cells : List ClassifiedCellInput) : Option (List String × String) := do
  let document ← document? cells
  let context := document.scalarComputationContext world
  let verdict (condition : ComputationCondition) : String :=
    match condition.eval context with
    | .holds => "1" | .notTrue => "-" | .poison _ => "P"
  let validation (leaf : FlatConditionLeaf) : String :=
    match FlatCondition.evalFull document.flatContext true (.leaf leaf) with
    | .fired _ => "1" | .notFired => "-" | .unknown => "P"
  let fields := [pd, py, fy, gf]
  let presence := fields.flatMap fun field =>
    [verdict (.fieldFilled field.id), verdict (.fieldNotFilled field.id)]
  let validated ← fields.flatMapM fun field => do
    let target ← flatField field
    pure [validation (.fieldFilled target), validation (.fieldNotFilled target)]
  if validated != presence then none
  let observations ← fields.mapM fun field =>
    (document.read { field := field.id, path := [] }).toOption.map (observeCell .validation)
  let count := match numberOfFilledFields observations with
    | .value count => toString count
    | .unknown => "-"
  pure (presence, count)

/- Row `p1`: two partially known values and two component-omitting ones, which the Kernel decodes to
their earliest date, are all filled, and the count is `4`. -/
example :
    answers? [cell pd "2024-06-00" (partialRaw pd "2024-06-00"),
      cell py "0000-00-00" (partialRaw py "0000-00-00"),
      cell fy "2024-06" (dateValue 2024 6 1), cell gf "2024-06" (dateValue 2024 6 1)] =
      some (["1", "-", "1", "-", "1", "-", "1", "-"], "4") := by
  native_decide

/- Rows `p2` and `p3`: two fully known values count two, and an empty document counts zero. -/
example :
    answers? [cell pd "2024-06-15" (partialRaw pd "2024-06-15"),
      cell py "2024-06-15" (partialRaw py "2024-06-15")] =
      some (["1", "-", "1", "-", "-", "1", "-", "1"], "2") ∧
    answers? [] = some (["-", "1", "-", "1", "-", "1", "-", "1"], "0") := by
  native_decide

/- Row `p4`: `2024-00-00` omits more than `DAY_OPTIONAL` admits, a formal failure that poisons `PD`'s
presence tests and the count, while `YEAR_OPTIONAL` admits it. -/
example :
    answers? [cell pd "2024-00-00" (partialRaw pd "2024-00-00"),
      cell py "2024-00-00" (partialRaw py "2024-00-00")] =
      some (["P", "P", "1", "-", "-", "1", "-", "1"], "-") := by
  native_decide

/- The partially known arm is placed only for exactly the stored text its precision-partial declaration
admits as partially known, so it is refused carrying another text, a text the declaration refuses, a
fully known text, or on a component-omitting or fragment declaration, whose value is the earliest date.
A partially known text placed as present-empty or as a text value, the encodings the arm replaced, is
refused too. A temporal value beside it is admitted and reported by `temporallyCoherent` instead, as on
every temporal declaration, and a text value on any other temporal declaration is admitted for the
formal check to report. -/
example :
    (document? [cell pd "2024-06-00" .presentEmpty]).isNone ∧
    (document? [cell pd "2024-06-00" (.parsed (.str "2024-06-00"))]).isNone ∧
    (document? [cell pd "2024-06-00" (.parsed (.partialDate "2024-07-00"))]).isNone ∧
    (document? [cell pd "2024-00-00" (.parsed (.partialDate "2024-00-00"))]).isNone ∧
    (document? [cell pd "2024-06-15" (.parsed (.partialDate "2024-06-15"))]).isNone ∧
    (document? [cell gf "2024-06" (.parsed (.partialDate "2024-06"))]).isNone ∧
    (document? [cell gf "2024-06" .presentEmpty]).isNone ∧
    (document? [cell fy "2024-06" (.parsed (.partialDate "2024-06"))]).isNone ∧
    ((document? [cell pd "2024-06-00" (dateValue 2024 6 1)]).map (·.temporallyCoherent)) = some false ∧
    (document? [cell fy "2024-06" (.parsed (.str "2024-06"))]).isSome := by
  native_decide

/-- `FieldValuesNotUnique(PD, PE)`, `1` when it fires and `-` when not. -/
private def notUnique? (first second : String) : Option String := do
  let document ← document? [cell pd first (partialRaw pd first), cell pe second (partialRaw pe second)]
  let bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }
  let source ← (elaborateTemporalValuesNotUniqueSource model ["Pr"]
    { first := .field (bare "PD"), rest := [.field (bare "PE")] }).toOption
  match (source.evaluateCheckedDocumentValuesNotUnique document []).toOption with
  | some (.fired _) => some "1"
  | some .notFired => some "-"
  | _ => none

/- Rows `o1` to `o4` of the reader grid: equal partially known texts are not unique and distinct ones
are, and a partially known `2024-06-00` beside a fully known `2024-06-01` is unique though both complete
to the same first day, so the operator compares the stored text. -/
example :
    notUnique? "2024-06-00" "2024-06-00" = some "1" ∧
    notUnique? "2024-06-00" "2024-07-00" = some "-" ∧
    notUnique? "2024-06-00" "2024-06-01" = some "-" ∧
    notUnique? "2024-06-15" "2024-06-15" = some "1" := by
  native_decide

/- Rows `o1` and `o2`: a required field holding a partially known value raises no mandatory finding and
an empty one does, and the cell is group content, the predicate both `GroupFilled` and the once rule's
root gate read, which the Kernel answers filled and evaluated for a group and a root holding only it. -/
example :
    (do
      let document ← document? [cell pd "2024-06-00" (partialRaw pd "2024-06-00")]
      let target ← flatField pd
      let read ← (document.read { field := pd.id, path := [] }).toOption
      pure ((AbsoluteRequiredDecl.evaluate { target } document.flatContext) == .notRequired &&
        read.admitsGroupContent)) = some true ∧
    (do
      let document ← document? []
      let target ← flatField pd
      pure (AbsoluteRequiredDecl.evaluate { target } document.flatContext ==
        .mandatory mandatoryFieldMetadata)) = some true := by
  native_decide

end A12Kernel.Conformance.PartialDatePresence
