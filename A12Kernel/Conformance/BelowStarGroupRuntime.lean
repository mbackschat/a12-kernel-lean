import A12Kernel.Elaboration.FilledFieldGroupCount
import A12Kernel.Elaboration.TokenValueCount
import A12Kernel.Elaboration.BooleanValueCount
import A12Kernel.Elaboration.NumericAggregate

/-! # A fixed group below a starred level, read by every carrier that admits it

Kernel 30.8.1 admits `Rows*/Detail`, a fixed group inside the repeatable `Rows`, on
`NumberOfFilledFields`, the seven field-fill quantifiers and the three `NumberOfValueInFields` arms,
and its answers over eight documents are retained at the
[runtime checkpoint](../../docs/SOURCES.md#src-below-star-group-runtime). This module replays that
matrix through each carrier's own checked source. The operand reaches only the group's own fields,
in every row the star reopens and none beyond the declared maximum, and a count moves until every
declared slot below the star is filled.
-/

namespace A12Kernel.Conformance.BelowStarGroupRuntime

open A12Kernel

private def number : FieldPolicy := { kind := .number { scale := 0, signed := true } }

/-- The retained model: `Rows` (max 2) holds `Qty` directly and three fixed groups, one per value
    kind, so each value count reads a homogeneous group. -/
private def model : FlatModel :=
  { fields := [
      { id := 2, groupPath := ["Probe", "Rows"], name := "Qty", policy := number,
        repeatableScope := [10] },
      { id := 3, groupPath := ["Probe", "Rows", "Detail"], name := "Amount", policy := number,
        repeatableScope := [10] },
      { id := 4, groupPath := ["Probe", "Rows", "Detail"], name := "Extra", policy := number,
        repeatableScope := [10] },
      { id := 5, groupPath := ["Probe", "Rows", "Texts"], name := "Note",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 6, groupPath := ["Probe", "Rows", "Flags"], name := "Mark",
        policy := { kind := .boolean }, repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Probe", "Rows"], repeatability := some 2 }] }

private def belowRows (group : String) : SurfaceStarGroupPath :=
  { base := .relative 0
    groups := [{ name := "Rows", starred := true }, { name := group }] }

private inductive Cell where
  | num (value : Nat)
  | malformed
  | text (value : String)
  | flag (value : Bool)

private def Cell.input (field : FieldId) (row : Nat) : Cell → ClassifiedCellInput
  | .num value => { address := { field, path := [row] }, stored := toString value
                    raw := .parsed (.num value) }
  | .malformed => { address := { field, path := [row] }, stored := "bad"
                    raw := .rejected .malformed }
  | .text value => { address := { field, path := [row] }, stored := value
                     raw := .parsed (.str value) }
  | .flag value => { address := { field, path := [row] }, stored := booleanValueCountToken value
                     raw := .parsed (.bool value) }

private def verdictCode : Verdict → Char
  | .fired .value => 'v'
  | .fired .omission => 'o'
  | .notFired | .unknown => 'u'

/-- One `== k` rule per `k` in `0 ..< bound`, as the retained model states them. -/
private def equalities (operand : Option NumericOperand) (bound : Nat) : String :=
  String.ofList ((List.range bound).map fun (k : Nat) =>
    operand.elim 'u' fun operand =>
      verdictCode (NumericComparisonOp.equal.evalFixedRight operand (k : Rat)))

private def fillCode : Option ValidationFillOutcome → Char
  | some (.fired .value) => 'v'
  | some (.fired .omission) => 'o'
  | some .falseOrUnknown | none => 'u'

/-- The order of the retained `Q0`..`Q6` rules. -/
private def quantifiers : List FieldFillQuantifier :=
  [.allFieldsFilled, .noFieldFilled, .atLeastOneFieldFilled, .moreThanOneFieldFilled,
    .notAllFieldsFilled, .notExactlyOneFieldFilled, .fieldsNotCollectivelyFilled]

/-- The fired rules of one document as the retained `C`, `Q`, `N`, `T` and `B` vectors, or `none`
    when a source fails to elaborate. -/
private def reading (rows : List Nat) (cells : List (FieldId × Nat × Cell)) : Option String := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    cells := cells.map fun (field, row, cell) => cell.input field row }).toOption
  let filled ← (elaborateFilledFieldCountStarredGroupValidationSource model ["Probe"]
    { group := belowRows "Detail" }).toOption
  let amounts ← (elaborateNumberEntitySource model ["Probe"]
    { first := .starredGroup (belowRows "Detail"), rest := [] }).toOption
  let notes ← (elaborateTokenValueCountStarredGroupValidationSource model ["Probe"] "x"
    { group := belowRows "Texts" }).toOption
  let marks ← (elaborateBooleanValueCountSource model ["Probe"] true
    { first := .starredGroup (belowRows "Flags"), rest := [] }).toOption
  let count := (filled.evaluateCheckedDocumentValidationOperand? document []).toOption.join
  let fills := String.ofList (quantifiers.map fun operator =>
    fillCode (filled.evaluateCheckedDocumentValidationFill? operator document []).toOption.join)
  pure (" ".intercalate [
    equalities count 5,
    fills,
    equalities (amounts.evaluateCheckedDocumentValueCountValidation 4 document []).toOption 5,
    equalities (notes.evaluateCheckedDocumentValidation document []).toOption 3,
    equalities (marks.evaluateCheckedDocumentValidation document []).toOption 3])

private def filledRow (row : Nat) : List (FieldId × Nat × Cell) :=
  [(3, row, .num 4), (4, row, .num 4), (5, row, .text "x"), (6, row, .flag true)]

/- `qty-only` answers exactly as `empty`, so the row's own `Qty` never reaches the operand, and
   `over-limit-only` does too, so a third row is outside it. `full` types the count `VALUE` at four,
   two fields in each of two rows, where `full-then-empty-row` still grows at two, so the extent is
   not the declared fields; `empty` grows at zero, so it is not the instantiated slots either but the
   declared slots below the star. The malformed
   `Amount` leaves both Number counts unavailable while `AtLeastOneFieldFilled` fires on `Extra`. -/
example :
    [reading [] [],
     reading [1] [(2, 1, .num 4)],
     reading [1] [(3, 1, .num 4), (5, 1, .text "x"), (6, 1, .flag true)],
     reading [1, 2] (filledRow 1 ++ filledRow 2),
     reading [1, 2] (filledRow 1),
     reading [1] [(3, 1, .malformed), (4, 1, .num 4)],
     reading [1, 2, 3] [(3, 3, .num 4), (5, 3, .text "x"), (6, 3, .flag true)],
     reading [1, 2] [(3, 1, .num 3), (4, 1, .num 4), (5, 1, .text "y"), (6, 1, .flag false),
       (3, 2, .num 4)]] =
    [some "ouuuu uouuoou ouuuu ouu ouu",
     some "ouuuu uouuoou ouuuu ouu ouu",
     some "uouuu uuvuouo uouuu uou uou",
     some "uuuuv vuvvuvu uuuuv uuv uuv",
     some "uuouu uuvvovo uuouu uou uou",
     some "uuuuu uuvuouo uuuuu ouu ouu",
     some "ouuuu uouuoou ouuuu ouu ouu",
     some "uuuou uuvvovo uuouu ouu ouu"] := by
  native_decide

end A12Kernel.Conformance.BelowStarGroupRuntime
