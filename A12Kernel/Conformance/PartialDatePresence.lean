import A12Kernel.Elaboration.ScalarComputationRunResult
import A12Kernel.Elaboration.PartialDateInput
import A12Kernel.Semantics.FieldFillQuantifier

/-! # Presence of a partially known Date

Every row of the [presence grid](../../docs/sources/temporal-and-message-probes.md#src-partial-date-presence):
a `yyyy-MM-dd` Date at `DAY_OPTIONAL` (`PD`) and at `YEAR_OPTIONAL` (`PY`), a component-omitting
`yyyy-MM` Date (`FY`) and a `yyyy-MM` DateFragment (`GF`), each read by `FieldFilled`, `FieldNotFilled`
and one `NumberOfFilledFields` over all four. The Kernel answers both arms alike, so a row locks each
field's presence and the count.

The rows separate a partially known value, which is filled, from an empty cell, which is not, and both
from a value deeper than its precision admits, which is a formal failure reached by both presence tests
and by the count. A model reading a partially known value as present-empty, the encoding a stored text
with no value would give, answers the first row as the third.
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

private def model : FlatModel := { fields := [pd, py, fy, gf] }

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

/-- Each field's `FieldFilled` and `FieldNotFilled` verdict, `1` for holds, `-` for not and `P` for
poison, and the four fields' filled count, `-` when unavailable. -/
private def answers? (cells : List ClassifiedCellInput) : Option (List String × String) := do
  let document ← document? cells
  let context := document.scalarComputationContext world
  let verdict (condition : ComputationCondition) : String :=
    match condition.eval context with
    | .holds => "1" | .notTrue => "-" | .poison _ => "P"
  let presence := [pd, py, fy, gf].flatMap fun field =>
    [verdict (.fieldFilled field.id), verdict (.fieldNotFilled field.id)]
  let observations ← [pd, py, fy, gf].mapM fun field =>
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

/- The partially known value has one encoding. A stored text beside no value, which would read as
present-empty, and a text value, which no Date admits, are refused; so is the partial arm carrying a
text other than the stored one, or one its declaration does not admit, or one on a component-omitting
or fragment declaration, whose value is the earliest date. -/
example :
    (document? [cell pd "2024-06-00" .presentEmpty]).isNone ∧
    (document? [cell pd "2024-06-00" (.parsed (.str "2024-06-00"))]).isNone ∧
    (document? [cell pd "2024-06-00" (.parsed (.partialDate "2024-07-00"))]).isNone ∧
    (document? [cell pd "2024-00-00" (.parsed (.partialDate "2024-00-00"))]).isNone ∧
    (document? [cell gf "2024-06" (.parsed (.partialDate "2024-06"))]).isNone ∧
    (document? [cell gf "2024-06" .presentEmpty]).isNone ∧
    (document? [cell fy "2024-06" (.parsed (.partialDate "2024-06"))]).isNone := by
  native_decide

end A12Kernel.Conformance.PartialDatePresence
