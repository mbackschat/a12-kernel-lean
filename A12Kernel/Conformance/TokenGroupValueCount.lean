import A12Kernel.Elaboration.TokenValueCount

/-! # Checked starred String-group value-count conformance

The maintained Kernel differentials admit one terminal repeatable starred String group as the whole operand list and reach matches across every expanded declaration and instantiated row. Checked computation additionally selects only in-capacity cells before classifying their String content. The explicit two-star source is the full-validation control. A separate Kernel admission row admits one fixed nonrepeatable String group; its checked runtime remains internal. A star above a nonrepeatable terminal remains refused.
-/

namespace A12Kernel

private def model : FlatModel :=
  { fields := [
      { id := 30, groupPath := ["Order", "Lines"], name := "A",
        policy := { kind := .string }, repeatableScope := [30],
        stringPolicy := { maxLength := some 1 } },
      { id := 31, groupPath := ["Order", "Lines"], name := "B",
        policy := { kind := .string }, repeatableScope := [30],
        stringPolicy := { maxLength := some 1 } }]
    repeatableGroups := [{
      level := 30, path := ["Order", "Lines"], repeatability := some 2 }] }

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def row (index : Nat) : RowAddr :=
  { group := 30, path := [index] }

private def cell (field : FieldId) (index : Nat)
    (value : String) : ClassifiedCellInput :=
  { address := { field, path := [index] }
    stored := value
    raw := .parsed (.str value) }

private def emptyCell (field : FieldId) (index : Nat) : ClassifiedCellInput :=
  { address := { field, path := [index] }
    stored := ""
    raw := .presentEmpty }

private def checkedDocument? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def star (field : String) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Order" }, { name := "Lines", starred := true }]
    field }

private def groupSource :
    SurfaceTokenValueCountStarredGroupValidationSource :=
  SurfaceTokenValueCountStarredGroupValidationSource.mk {
    base := .absolute
    groups := [{ name := "Order" }, { name := "Lines", starred := true }] }

private def checkedGroup? : Option (CheckedTokenValueCountGroupSource model) :=
  (elaborateTokenValueCountStarredGroupSource
    model ["Order"] "X" groupSource).toOption

private def explicitSource : SurfaceTokenValueCountSource :=
  { first := .star (star "A") .stored
    rest := [.star (star "B") .stored] }

private def document? : Option (CheckedDocument model) :=
  checkedDocument? [row 1, row 2] [
    cell 30 1 "X", cell 31 1 "Y", cell 30 2 "Y", cell 31 2 "X"]

private def evaluate? {candidate : FlatModel}
    (document? : Option (CheckedDocument candidate))
    (checked? : Option (CheckedTokenValueCountSource candidate)) :
    Option NumericOperand := do
  let checked ← checked?
  let document ← document?
  (checked.evaluateCheckedDocumentValidation document []).toOption

private def groupResult : Option NumericOperand := do
  let checked ← checkedGroup?
  let document ← document?
  (checked.evaluateCheckedDocumentValidation document []).toOption

private def compatibilityGroupResult : Option NumericOperand :=
  evaluate? document?
    (elaborateTokenValueCountStarredGroupValidationSource
      model ["Order"] "X" groupSource).toOption

private def explicitResult : Option NumericOperand :=
  evaluate? document? (elaborateTokenValueCountSource model ["Order"] "X"
    explicitSource).toOption

example :
    groupResult = some (.value 2 .fixed) ∧
      compatibilityGroupResult = some (.value 2 .fixed) ∧
      explicitResult = some (.value 2 .fixed) := by
  native_decide

private def computation? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← checkedGroup?
  let document ← checkedDocument? rows cells
  (checked.evaluateCheckedDocumentComputation document []).toOption

/- The checked computation reaches every declaration in every in-capacity row. -/
example :
    computation? [row 1, row 2] [
      cell 30 1 "X", cell 31 1 "Y", cell 30 2 "Y", cell 31 2 "X"] =
        some (.value 2 .fixed) ∧
      computation? [row 1, row 2] [
        cell 30 1 "X", cell 31 1 "Y", cell 30 2 "Y", cell 31 2 "Y"] =
          some (.value 1 .fixed) := by
  native_decide

/- Instantiated empty cells retain growth, while an absent group extent has the exact identity. -/
example :
    computation? [row 1, row 2] [
      emptyCell 30 1, emptyCell 31 1, emptyCell 30 2, emptyCell 31 2] =
        some (.value 0 .growOnly) ∧
      computation? [] [] = some (.value 0 .fixed) := by
  native_decide

/- A malformed reached cell poisons the count after an earlier match. -/
example :
    computation? [row 1, row 2] [
      cell 30 1 "X", cell 31 1 "Y", cell 30 2 "bad", cell 31 2 "Y"] =
        some (.unknown .declaredConstraint) := by
  native_decide

private def overCapacityRows : List RowAddr :=
  [row 1, row 2, row 3]

private def validation? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← checkedGroup?
  let document ← checkedDocument? rows cells
  (checked.evaluateCheckedDocumentValidation document []).toOption

/- Full validation retains the over-capacity cell and its formal cause. -/
example :
    validation? overCapacityRows [
      cell 30 1 "Y", cell 31 1 "Y", cell 30 2 "Y", cell 31 2 "Y",
      cell 30 3 "X", cell 31 3 "Y"] =
        some (.unknown .overRepetition) := by
  native_decide

/- An over-capacity match stays outside the computation domain. -/
example :
    computation? overCapacityRows [
      cell 30 1 "Y", cell 31 1 "Y", cell 30 2 "Y", cell 31 2 "Y",
      cell 30 3 "X", cell 31 3 "Y"] = some (.value 0 .fixed) := by
  native_decide

/- Excluding the over-capacity row preserves an in-capacity match. -/
example :
    computation? overCapacityRows [
      cell 30 1 "X", cell 31 1 "Y", cell 30 2 "Y", cell 31 2 "Y",
      cell 30 3 "X", cell 31 3 "Y"] = some (.value 1 .fixed) := by
  native_decide

/- Over-capacity malformed content remains outside the computation domain too. -/
example :
    computation? overCapacityRows [
      cell 30 1 "X", cell 31 1 "Y", cell 30 2 "Y", cell 31 2 "Y",
      cell 30 3 "bad", cell 31 3 "Y"] = some (.value 1 .fixed) := by
  native_decide

/-! ## Fixed group authoring -/

private def fixedModel : FlatModel :=
  { fields := [
      { id := 40, groupPath := ["Order", "Contact"], name := "Email",
        policy := { kind := .string } },
      { id := 41, groupPath := ["Order", "Contact"], name := "Phone",
        policy := { kind := .string } }] }

private def fixedPrepared :
    PreparedFlatStringContext fixedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler fixedModel).toOption.get (by native_decide)

private def fixedSource : SurfaceTokenValueCountFixedGroupValidationSource :=
  { group := {
      base := .absolute
      groups := ["Order", "Contact"] } }

private def fixedExplicitSource : SurfaceTokenValueCountSource :=
  { first := .field (.direct {
      base := .absolute, groups := ["Order", "Contact"], field := "Email" })
    rest := [.field (.direct {
      base := .absolute, groups := ["Order", "Contact"], field := "Phone" })] }

private def fixedDocument? : Option (CheckedDocument fixedModel) :=
  (checkDocument fixedPrepared "en_US" {
    instantiatedRows := []
    cells := [
      { address := { field := 40, path := [] }, stored := "X",
        raw := .parsed (.str "X") },
      { address := { field := 41, path := [] }, stored := "X",
        raw := .parsed (.str "X") }] }).toOption

private def fixedResult : Option NumericOperand :=
  evaluate? fixedDocument? (elaborateTokenValueCountFixedGroupValidationSource
    fixedModel ["Order"] "X" fixedSource).toOption

private def fixedExplicitResult : Option NumericOperand :=
  evaluate? fixedDocument? (elaborateTokenValueCountSource fixedModel ["Order"] "X"
    fixedExplicitSource).toOption

example :
    fixedResult = some (.value 2 .fixed) ∧
      fixedExplicitResult = some (.value 2 .fixed) := by
  native_decide

private def nonrepeatableTerminalModel : FlatModel :=
  { fields := [{
      id := 32, groupPath := ["Orders", "Details"], name := "A",
      policy := { kind := .string }, repeatableScope := [32] }]
    repeatableGroups := [{
      level := 32, path := ["Orders"], repeatability := some 2 }] }

private def nonrepeatableTerminalError : Option TokenValueCountElabError :=
  match elaborateTokenValueCountStarredGroupValidationSource
      nonrepeatableTerminalModel ["Orders"] "X" {
        group := {
          base := .absolute
          groups := [
            { name := "Orders", starred := true }, { name := "Details" }] } } with
  | .ok _ => none
  | .error error => some error

example :
    nonrepeatableTerminalError = some (.source (.shape (.starredGroup
      (.resolve (.unknownRepeatableGroup ["Orders", "Details"]))))) := by
  native_decide

end A12Kernel
