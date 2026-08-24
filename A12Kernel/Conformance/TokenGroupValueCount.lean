import A12Kernel.Elaboration.TokenValueCount

/-! # Checked starred String-group value-count conformance

The maintained Kernel differential admits one terminal repeatable starred String group as the whole operand list and reaches matches across every expanded declaration and instantiated row. The explicit two-star source is the same-fixture control. A separate Kernel admission row admits one fixed nonrepeatable String group; its checked runtime remains internal. A star above a nonrepeatable terminal remains refused.
-/

namespace A12Kernel

private def model : FlatModel :=
  { fields := [
      { id := 30, groupPath := ["Order", "Lines"], name := "A",
        policy := { kind := .string }, repeatableScope := [30] },
      { id := 31, groupPath := ["Order", "Lines"], name := "B",
        policy := { kind := .string }, repeatableScope := [30] }]
    repeatableGroups := [{
      level := 30, path := ["Order", "Lines"], repeatability := some 2 }] }

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def star (field : String) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Order" }, { name := "Lines", starred := true }]
    field }

private def groupSource :
    SurfaceTokenValueCountStarredGroupValidationSource :=
  { group := {
      base := .absolute
      groups := [{ name := "Order" }, { name := "Lines", starred := true }] } }

private def explicitSource : SurfaceTokenValueCountSource :=
  { first := .star (star "A") .stored
    rest := [.star (star "B") .stored] }

private def document? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 30, path := [1] }, { group := 30, path := [2] }]
    cells := [
      { address := { field := 30, path := [1] }, stored := "X",
        raw := .parsed (.str "X") },
      { address := { field := 31, path := [1] }, stored := "other",
        raw := .parsed (.str "other") },
      { address := { field := 30, path := [2] }, stored := "other",
        raw := .parsed (.str "other") },
      { address := { field := 31, path := [2] }, stored := "X",
        raw := .parsed (.str "X") }] }).toOption

private def evaluate? {candidate : FlatModel}
    (document? : Option (CheckedDocument candidate))
    (checked? : Option (CheckedTokenValueCountSource candidate)) :
    Option NumericOperand := do
  let checked ← checked?
  let document ← document?
  (checked.evaluateCheckedDocumentValidation document []).toOption

private def groupResult : Option NumericOperand :=
  evaluate? document? (elaborateTokenValueCountStarredGroupValidationSource
    model ["Order"] "X" groupSource).toOption

private def explicitResult : Option NumericOperand :=
  evaluate? document? (elaborateTokenValueCountSource model ["Order"] "X"
    explicitSource).toOption

example :
    groupResult = some (.value 2 .fixed) ∧
      explicitResult = some (.value 2 .fixed) := by
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
