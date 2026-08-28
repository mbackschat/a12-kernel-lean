import A12Kernel.Conformance.NumericComputation.Support
import A12Kernel.Elaboration.AddressedNumberFirstFilledComputation
import A12Kernel.Elaboration.AddressedNumberFirstFilledGeneratedValidation
import A12Kernel.Elaboration.NumericComputation.FormalInput

/-! # Numeric-computation repeatable locks -/

namespace A12Kernel.Conformance.NumericComputation.Repeatable

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

/- Computation consumes the same resolved aggregate source and fold: empties are skipped, all-empty is zero, and reached formal invalidity poisons. -/
example :
    checkedResultOf (surfaceAggregate .sum "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 4)))
          (checkedNumber (.parsed (.num 6)))) = some (.value 10) ∧
      checkedResultOf (surfaceAggregate .sum "Source" ["Later"]) =
        some (.value 0) ∧
      checkedResultOf (surfaceAggregate .minimum "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 20)))) = some (.value 20) ∧
      checkedResultOf (surfaceAggregate .maximum "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 20)))
          (checkedNumber (.rejected .declaredConstraint))) =
        some (.poison .declaredConstraint) := by
  native_decide

/- Direct Number `FirstFilledValue` becomes one ordinary numeric atom: prefix value/poison, exhaustion, arithmetic, and declaration-owned target checking retain their established meanings. -/
example :
    let expression := surfaceFirstFilled
      (.field (surfacePath ["Root"] "Source"))
      [.field (surfacePath ["Root"] "Later")]
    checkedCompleteScalarResultOf expression
        (context (checkedNumber .empty)
          (checkedNumber (.parsed (.num 7)))) = some (.value 7) ∧
      checkedCompleteScalarResultOf expression = some (.value 0) ∧
      checkedCompleteScalarResultOf expression
        (context (checkedNumber (.rejected .malformed))
          (checkedNumber (.parsed (.num 7)))) = some (.poison .malformed) ∧
      checkedCompleteScalarResultOf
        (.binary .add expression (.literal { value := 2, authoredScale := 0 }))
        (context (checkedNumber .empty)
          (checkedNumber (.parsed (.num 7)))) = some (.value 9) ∧
      checkedCompleteTargetResultOf expression
        (firstFilledContext (checkedNumber .empty)
          emptyNumberRows emptyNumberRows) =
        some (.supported (.rejected
          { unscaled := 0, scale := 0 } .zeroNotAllowed)) := by
  native_decide

/- Plain-star no-row selection falls through to a direct fallback, while a sole exhausted star remains Number zero. -/
example :
    let input := firstFilledContext (checkedNumber .empty)
      emptyNumberRows emptyNumberRows
      (checkedNumber (.parsed (.num 7))) []
    checkedCompleteResultOf
        (surfaceFirstFilled (.star repeatedStarPath)
          [.field (surfacePath ["Root"] "Later")]) input = some (.value 7) ∧
      checkedCompleteResultOf
        (surfaceFirstFilled (.star repeatedStarPath) []) input = some (.value 0) := by
  native_decide

/- The shared kept-successor traversal exposes an invalid immediate successor filter before the current target, but hides a third filter after one successor and hides the complete later slot after a direct terminal value. -/
example :
    let current := numberCells3 (.parsed (.num 5)) .empty .empty
    let immediatePoison := firstFilledContext
      (checkedNumber (.parsed (.num 1)))
      (numberCells3 (.parsed (.num 1)) (.rejected .malformed) .empty) current
    let hiddenThird := firstFilledContext
      (checkedNumber (.parsed (.num 1)))
      (numberCells3 (.parsed (.num 1)) (.parsed (.num 1))
        (.rejected .declaredConstraint)) current
    let directFirst := surfaceFirstFilled
      (.field (surfacePath ["Root"] "Source"))
      [.starHaving repeatedStarPath (repeatedAggregateHaving "Source")]
    checkedCompleteResultOf surfaceRepeatableFirstFilled immediatePoison =
        some (.poison .malformed) ∧
      checkedCompleteResultOf surfaceRepeatableFirstFilled hiddenThird =
        some (.value 5) ∧
      checkedCompleteResultOf directFirst
        (firstFilledContext (checkedNumber (.parsed (.num 9)))
          (numberCells3 (.rejected .malformed) .empty .empty)
          (numberCells3 (.rejected .declaredConstraint) .empty .empty)) =
        some (.value 9) := by
  native_decide

/- Repeatable evaluation remains addressed and target references are traversed through both selected fields and `Having`. -/
example :
    let malformed : NumericComputationEvaluationContext := {
      firstFilledContext (checkedNumber (.parsed (.num 1)))
        emptyNumberRows emptyNumberRows with
      document := {
        instantiatedRows := [{ group := 10, path := [1, 2] }]
        rawCells := fun _ => none } }
    checkedCompleteScalarFaultOf surfaceRepeatableFirstFilled =
        some .repeatableContextRequired ∧
      checkedCompleteFaultOf surfaceRepeatableFirstFilled malformed =
        some (.repeatableAddressing (.invalidRowDepth 10 [1, 2] 1)) ∧
      checkedCompleteErrorOf
        (surfaceFirstFilled (.field (surfacePath ["Root"] "Target"))
          [.field (surfacePath ["Root"] "Source")]) =
        some (.targetSelfReference targetId) ∧
      checkedCompleteErrorOf (surfaceRepeatableFirstFilled "Target") =
        some (.targetSelfReference targetId) := by
  native_decide

/- A filtered repeatable aggregate is one ordinary numeric atom: it composes with arithmetic and reaches the existing target checker without a top-level special path. -/
example :
    let rows := cells3
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 5)))
    let input := repeatableContext
      (checkedNumber (.parsed (.num 3))) rows
    let expression :=
      AuthoredNumericExpr.binary .add
        (surfaceRepeatableAggregate .sum)
        (.literal { value := 1, authoredScale := 0 })
    checkedRepeatableResultOf expression input = some (.value 7) ∧
      checkedRepeatableTargetResultOf expression input =
        some (.supported (.accepted { unscaled := 7, scale := 0 })) := by
  native_decide

/- A checked value count composes in the same expression and target path while retaining its selected source certificate. -/
example :
    let rows := cells3
      (checkedNumber (.parsed (.num 5)))
      (checkedNumber (.parsed (.num 7)))
      (checkedNumber (.parsed (.num 5)))
    let input := repeatableContext
      (checkedNumber (.parsed (.num 5))) rows
    let repeatedExpression :=
      AuthoredNumericExpr.binary .add
        (surfaceRepeatableValueCount 5)
        (.literal { value := 1, authoredScale := 0 })
    let directExpression := surfaceValueCount 5
      (.field (surfacePath ["Root"] "Source"))
      [.field (surfacePath ["Root"] "Later")]
    checkedCompleteResultOf repeatedExpression input = some (.value 3) ∧
      checkedCompleteTargetResultOf repeatedExpression input =
        some (.supported (.accepted { unscaled := 3, scale := 0 })) ∧
      checkedCompleteScalarResultOf directExpression
        (context (checkedNumber (.parsed (.num 5)))
          (checkedNumber (.parsed (.num 7)))) =
        some (.value 1) ∧
      checkedCompleteScalarFaultOf (surfaceRepeatableValueCount 5) =
        some .repeatableContextRequired ∧
      checkedCompleteErrorOf
        (surfaceValueCount 5
          (.field (surfacePath ["Root"] "Target"))
          [.field (surfacePath ["Root"] "Source")]) =
        some (.targetSelfReference targetId) := by
  native_decide

/- String/stored-Enumeration value count enters the same numeric expression and Number-target path while retaining exact token-domain and addressed-filter certificates. -/
example :
    let filterRows := cells3
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 5)))
    let tokenRows := cells3
      (formalCheck { kind := .string } (.parsed (.str "A")))
      (formalCheck { kind := .string } (.parsed (.str "B")))
      (formalCheck { kind := .string } (.parsed (.str "A")))
    let input := firstFilledContext
      (checkedNumber (.parsed (.num 3))) filterRows tokenRows
    let repeatedExpression :=
      AuthoredNumericExpr.binary .add
        (surfaceRepeatableTokenValueCount "A")
        (.literal { value := 1, authoredScale := 0 })
    let directExpression := surfaceTokenValueCount "2"
      (.field (.direct (surfacePath ["Root"] "Wrong")))
      [.field (.direct (surfacePath ["Root"] "NumericChoice"))]
    let categoryExpression := surfaceTokenValueCount "5"
      (.field (.category
        (surfacePath ["Root"] "NumericChoice") "Factor"))
      [.field (.direct (surfacePath ["Root"] "Wrong"))]
    let categoryScalar := context
      (code := formalCheck { kind := .string } (.parsed (.str "5")))
      (choice := formalCheck { kind := .enumeration }
        (.parsed (.enum "-150")))
    let malformedDocument : Document := {
      instantiatedRows := [{ group := 10, path := [1, 2] }]
      rawCells := fun _ => none }
    checkedCompleteResultOf repeatedExpression input = some (.value 2) ∧
      checkedCompleteTargetResultOf repeatedExpression input =
        some (.supported (.accepted { unscaled := 2, scale := 0 })) ∧
      checkedCompleteScalarResultOf directExpression
        (context
          (code := formalCheck { kind := .string } (.parsed (.str "2")))
          (choice := formalCheck { kind := .enumeration }
            (.parsed (.enum "2")))) =
        some (.value 2) ∧
      checkedCompleteScalarResultOf categoryExpression categoryScalar =
        some (.value 2) ∧
      checkedCompleteTargetResultOf categoryExpression
        { input with scalar := categoryScalar } =
        some (.supported (.accepted { unscaled := 2, scale := 0 })) ∧
      checkedCompleteScalarFaultOf
        (surfaceRepeatableTokenValueCount "A") =
        some .repeatableContextRequired ∧
      checkedCompleteFaultOf repeatedExpression
        { input with document := malformedDocument } =
        some (.repeatableAddressing (.invalidRowDepth 10 [1, 2] 1)) ∧
      checkedCompleteErrorOf
        (surfaceTokenValueCount "missing"
          (.field (.direct (surfacePath ["Root"] "Wrong")))
          [.field (.direct (surfacePath ["Root"] "NumericChoice"))]) =
        some (.tokenValueCount
          (.literalOutsideEnumerationDomain
            ["Root", "NumericChoice"] "missing")) := by
  native_decide

/- A repeatable aggregate never degrades into a scalar empty-document result, and malformed row topology stays an explicit addressing fault. -/
example :
    let rows := cells3
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 5)))
    let input := repeatableContext
      (checkedNumber (.parsed (.num 3))) rows
    let malformedDocument : Document := {
      instantiatedRows := [{ group := 10, path := [1, 2] }]
      rawCells := fun _ => none }
    checkedRepeatableScalarFaultOf
        (surfaceRepeatableAggregate .sum) =
      some .repeatableContextRequired ∧
    checkedRepeatableFaultOf
        (surfaceRepeatableAggregate .sum)
        { input with document := malformedDocument } =
      some (.repeatableAddressing (.invalidRowDepth 10 [1, 2] 1)) := by
  native_decide

/- Computation target self-reference traverses both the entity-list targets and the `Having` filter tree. -/
example :
    let directTarget :
        AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource) :=
      .atom (.aggregate .sum {
        first := .field (surfacePath ["Root"] "Target")
        rest := [.star repeatedStarPath] })
    checkedRepeatableErrorOf directTarget =
        some (.targetSelfReference targetId) ∧
      checkedRepeatableErrorOf
        (surfaceRepeatableAggregate .sum "Target") =
        some (.targetSelfReference targetId) := by
  native_decide

/- NumberOfDifferentValues uses the same checked computation atom, drops empty cells, and preserves formal poison while exposing only the integral value. -/
example :
    checkedResultOf (surfaceAggregate .distinctCount "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 5)))
          (checkedNumber (.parsed (.num 5)))) = some (.value 1) ∧
      checkedResultOf (surfaceAggregate .distinctCount "Source" ["Later"])
        (context (checkedNumber .empty)
          (checkedNumber (.parsed (.num 5)))) = some (.value 1) ∧
      checkedResultOf (surfaceAggregate .distinctCount "Source" ["Later"])
        (context (checkedNumber (.rejected .declaredConstraint))
          (checkedNumber (.parsed (.num 5)))) =
        some (.poison .declaredConstraint) := by
  native_decide

/- Aggregate atoms compose through plain arithmetic and the kernel-established direct rounding route while retaining their derived scale. -/
example :
    checkedResultOf
      (.binary .add (surfaceAggregate .sum "Source" ["Later"])
        (.literal { value := 1, authoredScale := 0 }))
      (context (checkedNumber (.parsed (.num 4)))
        (checkedNumber (.parsed (.num 6)))) = some (.value 11) ∧
      checkedResultOf
        (.round .halfUp omittedRoundingPlaces
          (surfaceAggregate .sum "Source" ["Later"]))
        (context (checkedNumber (.parsed (.num 4)))
          (checkedNumber (.parsed (.num 6)))) = some (.value 10) := by
  native_decide

/- Direct aggregate `Abs` runs after the shared fold, including negative totals, all-empty zero, and exact poison. A wrapper may also consume a checked operand-list extremum. -/
example :
    let aggregate := surfaceAggregate .sum "Source" ["Later"]
    checkedResultOf (.abs aggregate)
        (context (checkedNumber (.parsed (.num (-10))))
          (checkedNumber (.parsed (.num 4)))) = some (.value 6) ∧
      checkedResultOf (.abs aggregate) = some (.value 0) ∧
      checkedResultOf (.abs aggregate)
        (context (checkedNumber (.rejected .declaredConstraint))) =
          some (.poison .declaredConstraint) ∧
      checkedResultOf
        (.abs (surfaceAggregate .minimum "Source" ["Later"]))
        (context (checkedNumber (.parsed (.num (-10))))
          (checkedNumber (.parsed (.num 4)))) = some (.value 10) ∧
      checkedResultOf
        (.abs (surfaceAggregate .maximum "Source" ["Later"]))
        (context (checkedNumber (.parsed (.num (-10))))
          (checkedNumber (.parsed (.num 4)))) = some (.value 4) ∧
      checkedResultOf
        (.abs (surfaceAggregate .distinctCount "Source" ["Later"]))
        (context (checkedNumber (.parsed (.num 5)))
          (checkedNumber (.parsed (.num 5)))) = some (.value 1) ∧
      checkedResultOf
        (.abs (AuthoredNumericExpr.extremumList .minimum aggregate
          [surfaceField ["Root"] "Source"]))
        (context (checkedNumber (.parsed (.num (-10))))
          (checkedNumber (.parsed (.num 4)))) = some (.value 10) := by
  native_decide

/- Shared aggregate lowering preserves its diagnostic owner and computation's nested target-reference rejection. -/
example :
    checkedErrorOf (surfaceAggregate .sum "Source" ["Wrong"]) =
        some (.aggregate (.fieldKindMismatch ["Root", "Wrong"] .string)) ∧
      checkedErrorOf (surfaceAggregate .sum "Source" ["Target"]) =
        some (.targetSelfReference targetId) := by
  native_decide

namespace AddressedFirstFilled

private def field (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (scale : Nat := 0) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale, signed := true } }
}

private def source := field 101 "Candidate" ["Parents", "Choices"] [100, 110]
private def fallback := field 107 "Fallback" ["Parents", "Fallbacks"] [100, 115]
private def target : FlatFieldDecl := {
  field 102 "Result" ["Parents", "Tasks"] [100, 120] with
  numericTargetConstraints := { maximum := some 9 }
}
private def scaledSource := field 103 "Scaled" ["Parents", "Choices"] [100, 110] 2
private def wrongSource : FlatFieldDecl := {
  id := 104, name := "Wrong", groupPath := ["Parents", "Choices"]
  repeatableScope := [100, 110], policy := { kind := .string }
}
private def unrelated := field 105 "Unrelated" ["Summary"] []
private def targetDescendantSource := field 106 "NestedCandidate"
  ["Parents", "Tasks", "Details"] [100, 120, 130]

private def addressedModel : FlatModel := {
  fields := [source, fallback, target, scaledSource, wrongSource, unrelated,
    targetDescendantSource]
  repeatableGroups := [
    { level := 100, path := ["Parents"], repeatability := some 4 },
    { level := 110, path := ["Parents", "Choices"], repeatability := some 3 },
    { level := 115, path := ["Parents", "Fallbacks"], repeatability := some 3,
      indexField := some fallback.id },
    { level := 120, path := ["Parents", "Tasks"], repeatability := some 3 },
    { level := 130, path := ["Parents", "Tasks", "Details"],
      repeatability := some 3 }]
}

private def siblingStarIn (group name : String) : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := group, starred := true }]
  field := name
}

private def siblingStar (name : String) : SurfaceStarFieldPath :=
  siblingStarIn "Choices" name

private def targetDescendantStar : SurfaceStarFieldPath := {
  base := .relative 0
  groups := [{ name := "Details", starred := true }]
  field := targetDescendantSource.name
}

private def operation? :
    Option (CheckedAddressedNumberFirstFilledComputation addressedModel) :=
  (checkAddressedNumberFirstFilledComputation addressedModel
    ["Parents", "Tasks"] target.id (siblingStar source.name)).toOption

private def multiOperation? :
    Option (CheckedAddressedNumberFirstFilledComputation addressedModel) :=
  (checkAddressedNumberFirstFilledComputation addressedModel
    ["Parents", "Tasks"] target.id (siblingStar source.name)
      [siblingStarIn "Fallbacks" fallback.name]).toOption

private def multiFormalPlanProjection? :
    Option (List FieldId × List FieldId) := do
  let operation ← multiOperation?
  let plan ← operation.formalInputPlan.toOption
  pure (plan.operandFields, plan.computedFields)

private def elabError? (checked :
    Except AddressedNumberFirstFilledComputationElabError
      (CheckedAddressedNumberFirstFilledComputation addressedModel)) :
    Option AddressedNumberFirstFilledComputationElabError :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- One or more sibling stars are admitted in authored order. Every operand retains its own Number-kind, placement, and exact-scale gate. -/
example :
    operation?.isSome = true ∧ multiOperation?.isSome = true ∧
    elabError? (checkAddressedNumberFirstFilledComputation addressedModel
      ["Parents", "Tasks"] target.id (siblingStar wrongSource.name)) =
        some (.operand 0 (.source (.fieldNotNumber wrongSource.path))) ∧
    elabError? (checkAddressedNumberFirstFilledComputation addressedModel
      ["Parents", "Tasks"] target.id (siblingStar source.name)
        [siblingStar scaledSource.name]) =
        some (.operand 1 (.scaleMismatch 0 2)) ∧
    elabError? (checkAddressedNumberFirstFilledComputation addressedModel
      ["Parents", "Tasks"] target.id targetDescendantStar) =
        some (.operand 0
          (.placement (.sourceScope targetDescendantSource.path))) := by
  native_decide

/- The whole-call plan preserves the complete authored source order and excludes the exact computed target in its separate role. -/
example : multiFormalPlanProjection? =
    some ([source.id, fallback.id], [target.id]) := by
  native_decide

private def prepared :
    PreparedFlatStringContext addressedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler addressedModel).toOption.get (by native_decide)

private def rows : List RowAddr :=
  [{ group := 100, path := [1] }, { group := 100, path := [2] },
    { group := 100, path := [3] }, { group := 100, path := [4] },
    { group := 110, path := [1, 1] }, { group := 110, path := [1, 2] },
    { group := 110, path := [1, 3] }, { group := 110, path := [2, 1] },
    { group := 110, path := [4, 1] },
    { group := 115, path := [1, 1] }, { group := 115, path := [1, 2] },
    { group := 115, path := [2, 1] },
    { group := 115, path := [2, 2] }, { group := 115, path := [4, 1] },
    { group := 120, path := [2, 1] }, { group := 120, path := [1, 2] },
    { group := 120, path := [3, 1] }, { group := 120, path := [4, 1] },
    { group := 120, path := [1, 1] }]

private def cell (id : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field := id, path }, stored, raw }

private def decimalCell (id : FieldId) (path : List Nat) (stored : String)
    (unscaled : Int) : ClassifiedCellInput := {
  address := { field := id, path }
  stored
  raw := .parsed (.num unscaled)
  numericDecimal := some { unscaled, scale := 0 }
}

private def documentWithRows? (selectedRows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (CheckedDocument addressedModel) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := selectedRows, cells }).toOption

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument addressedModel) :=
  documentWithRows? rows cells

private def input? : Option (CheckedDocument addressedModel) :=
  document? [
    cell source.id [1, 1] "" .presentEmpty,
    cell source.id [1, 2] "5" (.parsed (.num 5)),
    cell source.id [1, 3] "bad-tail" (.rejected .malformed),
    cell source.id [2, 1] "bad" (.rejected .malformed),
    cell source.id [4, 1] "12" (.parsed (.num 12)),
    decimalCell target.id [1, 1] "5" 5,
    decimalCell target.id [1, 2] "2" 2,
    decimalCell target.id [2, 1] "8" 8,
    decimalCell target.id [4, 1] "1" 1,
    decimalCell unrelated.id [] "7" 7]

private def multiInput? : Option (CheckedDocument addressedModel) :=
  document? [
    cell source.id [1, 1] "" .presentEmpty,
    cell source.id [1, 2] "5" (.parsed (.num 5)),
    cell source.id [1, 3] "bad-tail" (.rejected .malformed),
    cell source.id [4, 1] "12" (.parsed (.num 12)),
    cell fallback.id [1, 1] "6" (.parsed (.num 6)),
    cell fallback.id [1, 2] "6" (.parsed (.num 6)),
    cell fallback.id [2, 1] "7" (.parsed (.num 7)),
    cell fallback.id [2, 2] "7" (.parsed (.num 7)),
    cell fallback.id [4, 1] "6" (.parsed (.num 6)),
    decimalCell target.id [1, 1] "5" 5,
    decimalCell target.id [1, 2] "2" 2,
    decimalCell target.id [2, 1] "8" 8,
    decimalCell target.id [4, 1] "1" 1,
    decimalCell unrelated.id [] "7" 7]

private def addr (id : FieldId) (path : List Nat) : CellAddr := { field := id, path }
private def stored (unscaled : Int) : StoredNumber := { unscaled, scale := 0 }
private def formalFinding (id : FieldId) (path : List Nat)
    (cause : FormalCause) : ComputationFormalInputFinding := {
  address := addr id path
  cause
}

private def outcomes? : Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← operation?
  let input ← input?
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

private def multiOutcomes? : Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← multiOperation?
  let input ← multiInput?
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

private def multiCallerReadOutcomes? : Option
    (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← multiOperation?
  let input ← multiInput?
  let outcomes ← operation.executeWithRead input (fun address => do
    let base ← input.read address
    if address == addr source.id [1, 2] ||
        address == addr fallback.id [4, 1] then
      pure (base.withFinding .duplicateIndex)
    else
      pure base) |>.toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

private structure FormalInputSummary where
  findingsExact : Bool
  values : List (NumericComputedInstance CellAddr)
  errors : List (NumericComputedError CellAddr)
  cleared : List CellAddr
  numericMessagesEmpty : Bool
  deriving Repr, DecidableEq

private def multiFormalInputSummary? : Option FormalInputSummary := do
  let operation ← multiOperation?
  let input ← multiInput?
  let result ← operation.executeResultWithFormalInputs input |>.toOption
  let findings := result.formalErrorsInOperands
  pure {
    findingsExact := findings.length == 5 &&
      findings.contains (formalFinding source.id [1, 3] .malformed) &&
      findings.contains (formalFinding fallback.id [1, 1] .duplicateIndex) &&
      findings.contains (formalFinding fallback.id [1, 2] .duplicateIndex) &&
      findings.contains (formalFinding fallback.id [2, 1] .duplicateIndex) &&
      findings.contains (formalFinding fallback.id [2, 2] .duplicateIndex)
    values := result.numeric.withoutErrors
    errors := result.numeric.withErrors
    cleared := result.numeric.cleared
    numericMessagesEmpty := result.numeric.formalErrorsInOperands.isEmpty
  }

/- Target rows scan only their enclosing parent's source extent. Empty exhaustion is zero, a malformed prefix poisons, the selected value hides its malformed tail, and target rejection follows selection. -/
example : outcomes? = some [
    (addr target.id [2, 1], .inheritedPoison .malformed),
    (addr target.id [1, 2], .accepted (stored 5)),
    (addr target.id [3, 1], .accepted (stored 0)),
    (addr target.id [4, 1], .rejected (stored 12) .aboveMaximum),
    (addr target.id [1, 1], .accepted (stored 5))
  ] := by
  native_decide

/- Authored source extents exhaust left to right inside each enclosing parent. A selected value hides poison in both remaining cells and later operands; a later parent can fall through to its own second extent, and total exhaustion remains Number zero. -/
example : multiOutcomes? = some [
    (addr target.id [2, 1], .accepted (stored 7)),
    (addr target.id [1, 2], .accepted (stored 5)),
    (addr target.id [3, 1], .accepted (stored 0)),
    (addr target.id [4, 1], .rejected (stored 12) .aboveMaximum),
    (addr target.id [1, 1], .accepted (stored 5))
  ] := by
  native_decide

/- A caller-supplied leaf view can poison one reached source and one later hidden fallback without changing topology, target order, exhausted zero, or declaration-owned target rejection. -/
example : multiCallerReadOutcomes? = some [
    (addr target.id [2, 1], .accepted (stored 7)),
    (addr target.id [1, 2], .inheritedPoison .duplicateIndex),
    (addr target.id [3, 1], .accepted (stored 0)),
    (addr target.id [4, 1], .rejected (stored 12) .aboveMaximum),
    (addr target.id [1, 1], .inheritedPoison .duplicateIndex)
  ] := by
  native_decide

/- The whole call eagerly inventories the hidden malformed source tail and duplicate findings from the later star, keeps them out of Number's rendered-message channel, hides their runtime poison behind an earlier value, and reaches the same poison after first-source fallthrough. -/
example : multiFormalInputSummary? = some {
    findingsExact := true
    values := [
      { targetField := addr target.id [1, 2], value := stored 5 },
      { targetField := addr target.id [3, 1], value := stored 0 },
      { targetField := addr target.id [1, 1], value := stored 5 }]
    errors := [{
      targetField := addr target.id [4, 1]
      attempted := stored 12
      cause := .aboveMaximum
    }]
    cleared := [addr target.id [2, 1]]
    numericMessagesEmpty := true
  } := by
  native_decide

private structure Summary where
  values : List (NumericComputedInstance CellAddr)
  changes : List (NumericComputedInstance CellAddr)
  errors : List (NumericComputedError CellAddr)
  cleared : List CellAddr
  states : List NumericTargetState
  deriving Repr, DecidableEq

private def summary? : Option Summary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    decimalCell target.id [1, 1] "9" 9,
    decimalCell target.id [3, 1] "7" 7,
    decimalCell target.id [4, 1] "6" 6,
    decimalCell unrelated.id [] "4" 4]
  let result ← operation.executeResult input (fun _ => ()) [] |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  let addresses :=
    [[1, 1], [1, 2], [2, 1], [3, 1], [4, 1]].map (addr target.id) ++
      [addr unrelated.id []]
  pure {
    values := result.numeric.withoutErrors
    changes := result.numeric.withChanges
    errors := result.numeric.withErrors
    cleared := result.numeric.cleared
    states := addresses.map applied.stateAt
  }

/- Classification uses immutable exact source state. Separate-destination application changes only retained actions, so the unchanged target and unrelated Number remain the destination's values. -/
example : summary? = some {
    values := [
      { targetField := addr target.id [1, 2], value := stored 5 },
      { targetField := addr target.id [3, 1], value := stored 0 },
      { targetField := addr target.id [1, 1], value := stored 5 }]
    changes := [
      { targetField := addr target.id [1, 2], value := stored 5 },
      { targetField := addr target.id [3, 1], value := stored 0 }]
    errors := [{
      targetField := addr target.id [4, 1]
      attempted := stored 12
      cause := .aboveMaximum
    }]
    cleared := [addr target.id [2, 1]]
    states := [
      .presentValue (.decimal (stored 9)),
      .presentValue (.decimal (stored 5)),
      .presentEmpty,
      .presentValue (.decimal (stored 0)),
      .presentEmpty,
      .presentValue (.decimal (stored 4))]
  } := by
  native_decide

private def generatedMessagePlan : MessageRenderPlan :=
  { parts := [.text "Result disagrees with its computation"] }

private def generatedExpectedMessage (path : List Nat) : FlatRuleMessage := {
  errorAddress := MessagePointer.ofCellAddr (addr target.id path)
  errorCode := "computedNumberFirstFilled"
  severity := .error
  messageType := .omission
  text := generatedMessagePlan.render
}

private def generatedAppliedValidation? : Option
    (Summary × List (Env × FlatRuleOutcome)) := do
  let operation ← multiOperation?
  let sourceDocument ← multiInput?
  let destination ← document? [
    cell source.id [1, 1] "" .presentEmpty,
    cell source.id [1, 2] "5" (.parsed (.num 5)),
    cell fallback.id [2, 1] "8" (.parsed (.num 8)),
    decimalCell target.id [1, 1] "9" 9,
    decimalCell target.id [3, 1] "7" 7,
    decimalCell target.id [4, 1] "6" 6,
    decimalCell unrelated.id [] "4" 4]
  let run ← (operation.executeGeneratedAppliedValidation sourceDocument
    destination (fun _ => ()) [] "computedNumberFirstFilled"
    generatedMessagePlan).toOption
  let addresses :=
    [[2, 1], [1, 2], [3, 1], [4, 1], [1, 1]].map (addr target.id) ++
      [addr unrelated.id []]
  pure ({
    values := run.result.numeric.withoutErrors
    changes := run.result.numeric.withChanges
    errors := run.result.numeric.withErrors
    cleared := run.result.numeric.cleared
    states := addresses.map run.applied.stateAt
  }, run.validation)

/- The repeatable computation executes against its immutable source, applies only source-relative actions, and then validates every destination target row against destination sources. Parent two recomputes eight after source execution produced seven, so validation must follow application and reread the destination. Parent one's source-identical first target has no action and leaves the destination's stale nine to mismatch its recomputed five; reclassifying against the destination would erase that witness. The changed second target and parent three agree, while the errored fourth target is empty before the generated filled gate. -/
example : generatedAppliedValidation? = some ({
    values := [
      { targetField := addr target.id [2, 1], value := stored 7 },
      { targetField := addr target.id [1, 2], value := stored 5 },
      { targetField := addr target.id [3, 1], value := stored 0 },
      { targetField := addr target.id [1, 1], value := stored 5 }]
    changes := [
      { targetField := addr target.id [2, 1], value := stored 7 },
      { targetField := addr target.id [1, 2], value := stored 5 },
      { targetField := addr target.id [3, 1], value := stored 0 }]
    errors := [{
      targetField := addr target.id [4, 1]
      attempted := stored 12
      cause := .aboveMaximum
    }]
    cleared := []
    states := [
      .presentValue (.decimal (stored 7)),
      .presentValue (.decimal (stored 5)),
      .presentValue (.decimal (stored 0)),
      .presentEmpty,
      .presentValue (.decimal (stored 9)),
      .presentValue (.decimal (stored 4))]
  }, [
    ([(100, 2), (120, 1)],
      .fired (generatedExpectedMessage [2, 1])),
    ([(100, 1), (120, 2)], .notFired),
    ([(100, 3), (120, 1)], .notFired),
    ([(100, 4), (120, 1)], .notFired),
    ([(100, 1), (120, 1)],
      .fired (generatedExpectedMessage [1, 1]))
  ]) := by
  native_decide

private def generatedDestinationOnlyValidation? : Option
    (Bool × Option (Env × FlatRuleOutcome)) := do
  let operation ← multiOperation?
  let sourceDocument ← multiInput?
  let destinationRows := rows ++ [{ group := 120, path := [2, 2] }]
  let destination ← documentWithRows? destinationRows [
    cell fallback.id [2, 1] "8" (.parsed (.num 8)),
    decimalCell target.id [2, 2] "9" 9]
  let run ← (operation.executeGeneratedAppliedValidation sourceDocument
    destination (fun _ => ()) [] "computedNumberFirstFilled"
    generatedMessagePlan).toOption
  let targetAddress := addr target.id [2, 2]
  pure (
    run.result.numeric.withoutErrors.any fun value =>
      value.targetField == targetAddress,
    run.validation.find? fun entry =>
      entry.1 == [(100, 2), (120, 2)])

/- Validation enumerates destination target rows rather than source execution rows. A destination-only target has no source result, yet its filled nine mismatches the destination's fallback eight and fires at its exact address. -/
example : generatedDestinationOnlyValidation? = some (false,
    some ([(100, 2), (120, 2)],
      .fired (generatedExpectedMessage [2, 2]))) := by
  native_decide

private def generatedCreatedTopologyError? : Option
    AddressedNumberFirstFilledAppliedValidationError := do
  let operation ← multiOperation?
  let sourceDocument ← multiInput?
  let destinationRows := rows.erase { group := 120, path := [3, 1] }
  let destination ← documentWithRows? destinationRows []
  match operation.executeGeneratedAppliedValidation sourceDocument
      destination (fun _ => ()) [] "computedNumberFirstFilled"
      generatedMessagePlan with
  | .error cause => some cause
  | .ok _ => none

/- The bounded route refuses the first retained action whose ancestry application would create. Existing-row validation cannot silently stand in for materialized document topology. -/
example : generatedCreatedTopologyError? =
    some (.materializedTopology (addr target.id [3, 1])) := by
  native_decide

private def generatedCreatedTopologyOrderError? : Option
    AddressedNumberFirstFilledAppliedValidationError := do
  let operation ← operation?
  let sourceDocument ← input?
  let destinationRows :=
    (rows.erase { group := 120, path := [2, 1] }).erase
      { group := 120, path := [3, 1] }
  let destination ← documentWithRows? destinationRows []
  match operation.executeGeneratedAppliedValidation sourceDocument
      destination (fun _ => ()) [] "computedNumberFirstFilled"
      generatedMessagePlan with
  | .error cause => some cause
  | .ok _ => none

/- Topology refusal follows the established application action order: retained clears are examined before changed values. -/
example : generatedCreatedTopologyOrderError? =
    some (.materializedTopology (addr target.id [2, 1])) := by
  native_decide

private structure MaterializedGeneratedSummary where
  result : Summary
  outerRows : List RowAddr
  leafRows : List RowAddr
  validation : List (Env × FlatRuleOutcome)
  deriving Repr, DecidableEq

private def generatedMaterializedValidation? :
    Option MaterializedGeneratedSummary := do
  let operation ← operation?
  let sourceDocument ← input?
  let destinationRows := rows.filter fun row => row.group != 120
  let destination ← documentWithRows? destinationRows [
    cell source.id [1, 2] "6" (.parsed (.num 6)),
    decimalCell unrelated.id [] "4" 4]
  let run ← (operation.executeGeneratedMaterializedAppliedValidation
    sourceDocument destination (fun _ => ()) []
    "computedNumberFirstFilled" generatedMessagePlan).toOption
  let leafRows := run.applied.leafRows
  let addresses := leafRows.map fun row =>
    { field := target.id, path := row.path }
  pure {
    result := {
      values := run.result.numeric.withoutErrors
      changes := run.result.numeric.withChanges
      errors := run.result.numeric.withErrors
      cleared := run.result.numeric.cleared
      states := addresses.map run.applied.stateAt
    }
    outerRows := run.applied.outerRows
    leafRows
    validation := run.validation
  }

/- Two-level application materializes only target topology. The changed row `[1,2]` pads an empty predecessor, the retained clear creates `[2,1]`, the zero change creates `[3,1]`, and the errored `[4,1]` remains absent. Generated validation visits those normalized leaves in target order and recomputes parent one's source from the destination. -/
example : generatedMaterializedValidation? = some {
  result := {
    values := [
      { targetField := addr target.id [1, 2], value := stored 5 },
      { targetField := addr target.id [3, 1], value := stored 0 },
      { targetField := addr target.id [1, 1], value := stored 5 }]
    changes := [
      { targetField := addr target.id [1, 2], value := stored 5 },
      { targetField := addr target.id [3, 1], value := stored 0 }]
    errors := [{
      targetField := addr target.id [4, 1]
      attempted := stored 12
      cause := .aboveMaximum
    }]
    cleared := [addr target.id [2, 1]]
    states := [
      .absent,
      .presentValue (.decimal (stored 5)),
      .presentEmpty,
      .presentValue (.decimal (stored 0))]
  }
  outerRows :=
    [{ group := 100, path := [1] }, { group := 100, path := [2] },
      { group := 100, path := [3] }, { group := 100, path := [4] }]
  leafRows :=
    [{ group := 120, path := [1, 1] },
      { group := 120, path := [1, 2] },
      { group := 120, path := [2, 1] },
      { group := 120, path := [3, 1] }]
  validation := [
    ([(100, 1), (120, 1)], .notFired),
    ([(100, 1), (120, 2)],
      .fired (generatedExpectedMessage [1, 2])),
    ([(100, 2), (120, 1)], .notFired),
    ([(100, 3), (120, 1)], .notFired)
  ]
} := by
  native_decide

private def generatedThreeLevelScopeError? : Option
    AddressedNumberFirstFilledMaterializedAppliedValidationError := do
  let deepTarget := field 108 "DeepResult" ["Parents", "Tasks", "Details"] [100, 120, 130]
  let deepModel : FlatModel := { addressedModel with fields := deepTarget :: addressedModel.fields }
  let deepSource := { siblingStar source.name with base := .relative 2 }
  let operation ← (checkAddressedNumberFirstFilledComputation deepModel
    deepTarget.groupPath deepTarget.id deepSource).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler deepModel).toOption
  let document ← (checkDocument prepared "en_US"
    { instantiatedRows := [], cells := [] }).toOption
  errorOf <| operation.executeGeneratedMaterializedAppliedValidation
    document document (fun _ => ()) [] "computedNumberFirstFilled"
      generatedMessagePlan

/- A checked three-level target with a nonempty proper outer source prefix reaches the bounded continuation and is rejected before rule assembly or source execution. -/
example : generatedThreeLevelScopeError? =
    some (.targetScope [100, 120, 130]) := by
  native_decide

end AddressedFirstFilled


end A12Kernel.Conformance.NumericComputation.Repeatable
