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

private def formalRead (info : NumField) (constraints : NumericTargetConstraints)
    (input : NumericStoredInput) : Except NumericFormalReadError (String × Rat) :=
  constraints.checkFormalRead info input

-- a12-dmkits KF686 at 79a7171c8: on kernel 31.3.1 retained `001.20` meets a six-character minimum
-- that native `1.20`, native `1.2000` and converted `"1.20"` miss, and a rule reads its amount 1.2.
example :
    let info : NumField := { scale := 2, signed := true }
    let weight (minimum : Nat) : NumericTargetConstraints := {
      minFractionalDigits := 2, leadingZerosAllowed := true, minimum := some (6 / 5),
      maximum := some (6 / 5), minStoredLength := some minimum, maxStoredLength := some 6 }
    let inputs : List NumericStoredInput := [.text "001.20", .decimal { unscaled := 120, scale := 2 },
      .decimal { unscaled := 12000, scale := 4 }, .decimal { unscaled := 120, scale := 2 }]
    inputs.map (fun input => (formalRead info (weight 4) input).toOption) =
        [some ("001.20", 6 / 5), some ("1.20", 6 / 5), some ("1.20", 6 / 5), some ("1.20", 6 / 5)] ∧
    inputs.map (fun input => match formalRead info (weight 6) input with
        | .ok _ => none | .error error => some error) =
        [none, some .textTooShort, some .textTooShort, some .textTooShort] := by
  native_decide

-- a12-dmkits KF687 at 79a7171c8: on kernel 31.3.1 retained leading zeros count as digits toward the
-- fifteen-digit total and the integer-digit cap, measured on positive integer text of amount 1 only.
example :
    let info : NumField := { scale := 0, signed := true }
    let one (cap : Option Nat) : NumericTargetConstraints := {
      leadingZerosAllowed := true, minimum := some 1, maximum := some 1, maxIntegerDigits := cap }
    let errorOf (cap : Option Nat) (input : NumericStoredInput) :=
      match formalRead info (one cap) input with | .ok _ => none | .error error => some error
    let native : NumericStoredInput := .decimal { unscaled := 1, scale := 0 }
    [errorOf none native, errorOf none (.text "000000000000001"),
      errorOf none (.text "0000000000000001"),
      errorOf (some 2) native, errorOf (some 2) (.text "01"), errorOf (some 2) (.text "001"),
      errorOf (some 3) native, errorOf (some 3) (.text "01"), errorOf (some 3) (.text "001")] =
    [none, none, some .totalDigitsTooLong, none, none, some .integerDigitsTooLong, none, none, none] := by
  native_decide

end A12Kernel.Dm.NumberLengthLocks
