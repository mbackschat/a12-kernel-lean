import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Semantics.NumericComputationApplicationFold

namespace A12Kernel.Dm.NumberLengthLocks

private structure Summary where
  selectedText : String
  raw : RawCell
  equality : Verdict
  computed : NumericTargetOutcome
  changed : Nat
  applied : NumericTargetState
  deriving Repr, BEq

private def run (leadingZeros : Bool) (stored : String)
    (minimum maximum : Option Nat) : Option Summary := do
  let constraints : NumericTargetConstraints := {
    leadingZerosAllowed := leadingZeros
    minStoredLength := minimum
    maxStoredLength := maximum }
  let model : FlatModel := {
    fields := [{
      id := 1, name := "Amount", groupPath := ["Form"],
      policy.kind := .number { scale := 0, signed := true },
      numericTargetConstraints := constraints }] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (.mkObj [("Form", .mkObj [("Amount", .str stored)])])).toOption
  let cell ← data.data.cells.head?
  let selectedText := match cell.numericDecimal with
    | some decimal => decimal.formalReadText 0
    | none => cell.stored
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let parsed ← (parseText .english "[Amount] == 12").toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let equality ← (condition.core.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document }).toOption
  let (_, lowered) ← (lowerComputation model .english {
    name := "Replace", group := ["Form"], targetRelPath := "../Amount", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := "12" }], errorCodesToSuppress := [] }).toOption
  let .number table _ := lowered | none
  let plan ← (certifyAuthoredMixedComputationPlan
    ([.number table] : List (MixedComputationStep model builtinStringPatternCompiler))).toOption
  let outcomes ← (plan.execute world prepared.patterns document).toOption
  let entries := outcomes.filterMap fun | .number entry => some entry | _ => none
  let entry ← entries.head?
  let result := NumericComputationRunView.fromPartitionedSourceOutcomes ([] : List Unit) entries
  let applied ← (result.applyTo document.numericTargetPlacementStateAt).toOption
  pure {
    selectedText, raw := cell.raw, equality, computed := entry.outcome,
    changed := result.withChanges.length, applied := applied { field := 1, path := [] } }

private def twelve : StoredNumber := { unscaled := 12, scale := 0 }

private def expected (leadingZeros : Bool) (stored : String)
    (inputValid : Bool) (computed : NumericTargetOutcome) : Summary := {
  selectedText := if leadingZeros && stored == "0012" then "0012" else "12"
  raw := if inputValid then .parsed (.num 12) else .rejected .declaredConstraint
  equality := if inputValid then .fired .value else .unknown
  computed
  changed := match computed with
    | .accepted _ => if leadingZeros && stored == "0012" then 1 else 0
    | _ => 0
  applied := match computed with
    | .accepted value => .presentValue (.decimal value)
    | _ => .presentEmpty }

-- Spec §4's storage regimes distinguish lexical length from amount; computed output is canonical.
example : [false, true].all (fun leadingZeros =>
    ["0012", "12"].all (fun stored =>
      run leadingZeros stored none none == some (expected leadingZeros stored true (.accepted twelve)) &&
      run leadingZeros stored (some 2) (some 4) == some (expected leadingZeros stored true (.accepted twelve)) &&
      run leadingZeros stored (some 4) none == some (expected leadingZeros stored
        (leadingZeros && stored == "0012") (.rejected twelve .storedTextTooShort)) &&
      run leadingZeros stored (some 5) none == some (expected leadingZeros stored
        false (.rejected twelve .storedTextTooShort)) &&
      run leadingZeros stored none (some 1) == some (expected leadingZeros stored
        false (.rejected twelve .storedTextTooLong)) &&
      run leadingZeros stored none (some 2) == some (expected leadingZeros stored
        (!(leadingZeros && stored == "0012")) (.accepted twelve)))) = true := by
  native_decide

-- Exact formal causes are retained below the checked document's coarse declared-constraint cause.
example :
    let info : NumField := { scale := 0, signed := true }
    let constraints : NumericTargetConstraints := { leadingZerosAllowed := true }
    let errorOf := fun (result : Except NumericFormalReadError (String × Rat)) =>
      match result with | .error error => some error | .ok _ => none
    errorOf ({ constraints with minStoredLength := some 4 }.checkFormalRead info (.text "12")) =
      some .textTooShort ∧
    errorOf ({ constraints with maxStoredLength := some 2 }.checkFormalRead info (.text "0012")) =
      some .textTooLong ∧
    (constraints.checkFormalRead info (.text "0012")).toOption = some ("0012", 12) := by
  native_decide

-- Retained runtime-formal-number-cascade request2 rows w04/w05/w06 settle the lexical distinction.
example :
    let declaration : FlatFieldDecl := {
      id := 1, name := "LeadZeroOk", groupPath := ["FormalNum"]
      policy.kind := .number { scale := 0, signed := true }
      numericTargetConstraints := { leadingZerosAllowed := true, minStoredLength := some 4 } }
    [("0123", RawCell.parsed (.num 123)), ("0000", .parsed (.num 0)),
      ("25", .rejected .declaredConstraint)].all (fun (text, expected) =>
        ((classifyStored { fields := [declaration] } declaration { field := 1, path := [] } text).toOption.map
          (·.raw)) == some expected) = true := by
  native_decide

end A12Kernel.Dm.NumberLengthLocks
