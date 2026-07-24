import A12Kernel.Conformance.NumericComputation.Support

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

/- Fixed group counts remain validation-only until checked computation scheduling owns group-state dependencies and clearing. -/
example : checkedErrorOf surfaceFixedGroupCount = some .unsupportedExpression := by
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


end A12Kernel.Conformance.NumericComputation.Repeatable
