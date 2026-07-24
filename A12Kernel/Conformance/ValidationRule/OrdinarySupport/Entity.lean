import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Core

/-! # Shared ordinary repeatable entity and mixed-scope fixtures -/

namespace A12Kernel.Conformance.ValidationRule.OrdinarySupport

open A12Kernel

def deeperInnerAmountStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Order" },
      { name := "Sections" },
      { name := "Items", starred := true }]
    field := "InnerAmount" }

def deeperInnerPriceStar : SurfaceStarFieldPath :=
  { deeperInnerAmountStar with field := "InnerPrice" }

def deeperInnerTokenStar : SurfaceStarFieldPath :=
  { deeperInnerAmountStar with field := "InnerToken" }

def outerWithInnerAggregateCore? :
    Option (OrderedNumericComparison ordinaryIterationModel) := do
  let outerField ← outerAmount.toNumberField?
  let innerSource ←
    (elaborateNumberEntitySource ordinaryIterationModel
      ["Order", "Sections"] {
        first := .star deeperInnerAmountStar
        rest := []
      }).toOption
  let core : OrderedNumericComparison ordinaryIterationModel := {
    op := .ordinary .greater
    left := .binary .add
      (.atom (.ordinary (.field outerField)))
      (.atom (.aggregate .sum innerSource))
    right := .literal { value := 5, authoredScale := 0 }
  }
  pure core

def outerWithInnerAggregateComparison? :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let core ← outerWithInnerAggregateCore?
  if hCore : core.wellFormedInBool ["Order", "Sections"]
      .sameGroupAddressed = true then
    pure {
      rowGroup := ["Order", "Sections"]
      operandScope := .sameGroupAddressed
      core
      modelWellFormed := by native_decide
      wellFormed := hCore
    }
  else
    none

def outerWithInnerAggregateRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let numeric ← outerWithInnerAggregateComparison?
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition outerAmount.id
    "outerWithInnerAggregate" .error { parts := [] }).toOption

def innerAmountSelfHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner
      field := ordinaryPath ["Order", "Sections", "Items"] "InnerAmount" }
    { origin := .inner
      field := ordinaryPath ["Order", "Sections", "Items"] "InnerAmount" }

def innerAmountBaseHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .notEqual
    { origin := .inner
      field := ordinaryPath ["Order", "Sections", "Items"] "InnerAmount" }
    { origin := .inner
      field := ordinaryPath ["Order"] "BaseAmount" }

def deeperInnerNumberSource?
    (withFilteredDuplicate : Bool := false) :
    Option (CheckedNumberEntitySource ordinaryIterationModel) :=
  (elaborateNumberEntitySource ordinaryIterationModel
    ["Order", "Sections"] {
      first := .star deeperInnerAmountStar
      rest := if withFilteredDuplicate then
        [.starHaving deeperInnerAmountStar innerAmountSelfHaving]
      else []
    }).toOption

def mixedDirectStarNumberSource? :
    Option (CheckedNumberEntitySource ordinaryIterationModel) :=
  (elaborateNumberEntitySource ordinaryIterationModel
    ["Order", "Sections"] {
      first := .field (ordinaryPath ["Order"] "BaseAmount")
      rest := [.star deeperInnerAmountStar]
    }).toOption

def filterMixedReferenceNumberSource? :
    Option (CheckedNumberEntitySource ordinaryIterationModel) :=
  (elaborateNumberEntitySource ordinaryIterationModel
    ["Order", "Sections"] {
      first := .starHaving deeperInnerAmountStar innerAmountBaseHaving
      rest := []
    }).toOption

def checkedOuterEntityComparison?
    (core : OrderedNumericComparison ordinaryIterationModel) :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) :=
  if hCore : core.wellFormedInBool ["Order", "Sections"]
      .sameGroupAddressed = true then
    some {
      rowGroup := ["Order", "Sections"]
      operandScope := .sameGroupAddressed
      core
      modelWellFormed := by native_decide
      wellFormed := hCore
    }
  else
    none

def orderedAtomLiteralLegality?
    (atom : OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (literalValue : DecodedNumericLiteral)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let entity : AuthoredNumericExpr
      (OrderedNumericValidationAtom ordinaryIterationModel) :=
    .atom atom
  let literal : AuthoredNumericExpr
      (OrderedNumericValidationAtom ordinaryIterationModel) :=
    .literal literalValue
  let comparison ← checkedOuterEntityComparison? {
    op
    left := if literalOnLeft then literal else entity
    right := if literalOnLeft then entity else literal
  }
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric comparison).toOption
  condition.core.iterationLegality.toOption

def orderedAtomLegality?
    (atom : OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality :=
  orderedAtomLiteralLegality? atom op
    { value := expected, authoredScale := 0 } literalOnLeft

def numberEntityLegality?
    (source? : Option
      (CheckedNumberEntitySource ordinaryIterationModel))
    (atomOf : CheckedNumberEntitySource ordinaryIterationModel →
      OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let source ← source?
  orderedAtomLegality? (atomOf source) op expected literalOnLeft

def plainStarEntityLegality?
    (atomOf : CheckedNumberEntitySource ordinaryIterationModel →
      OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality :=
  numberEntityLegality? deeperInnerNumberSource? atomOf op expected literalOnLeft

def mixedDirectStarEntityLegality?
    (atomOf : CheckedNumberEntitySource ordinaryIterationModel →
      OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality :=
  numberEntityLegality? mixedDirectStarNumberSource?
    atomOf op expected literalOnLeft

def filteredEntityLegality?
    (atomOf : CheckedNumberEntitySource ordinaryIterationModel →
      OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat) :
    Option ValidationCondition.IterationLegality :=
  numberEntityLegality? (deeperInnerNumberSource? true) atomOf op expected

def filterMixedReferenceEntityLegality?
    (atomOf : CheckedNumberEntitySource ordinaryIterationModel →
      OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat) :
    Option ValidationCondition.IterationLegality :=
  numberEntityLegality? filterMixedReferenceNumberSource?
    atomOf op expected

def plainStarTokenValueCountSource? :
    Option (CheckedTokenValueCountSource ordinaryIterationModel) :=
  (elaborateTokenValueCountSource ordinaryIterationModel
    ["Order", "Sections"] "A" {
      first := .star deeperInnerTokenStar .stored
      rest := []
    }).toOption

def mixedTokenValueCountSource? :
    Option (CheckedTokenValueCountSource ordinaryIterationModel) :=
  (elaborateTokenValueCountSource ordinaryIterationModel
    ["Order", "Sections"] "A" {
      first := .field (.direct (ordinaryPath ["Order"] "BaseToken"))
      rest := [.star deeperInnerTokenStar .stored]
    }).toOption

def tokenValueCountLegality?
    (source? : Option
      (CheckedTokenValueCountSource ordinaryIterationModel))
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let source ← source?
  orderedAtomLegality? (.tokenValueCount source)
    op expected literalOnLeft

def outerWithInnerTokenValueCountRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let outerField ← outerAmount.toNumberField?
  let source ← plainStarTokenValueCountSource?
  let comparison ← checkedOuterEntityComparison? {
    op := .ordinary .greater
    left := .binary .add
      (.atom (.ordinary (.field outerField)))
      (.atom (.tokenValueCount source))
    right := .literal { value := 2, authoredScale := 0 }
  }
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric comparison).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition outerAmount.id
    "outerWithInnerTokenValueCount" .error { parts := [] }).toOption

def mixedScopeWrappedNumericLegality?
    (op : NumericValidationOp) (expected : Rat) :
    Option ValidationCondition.IterationLegality := do
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := .extremumCall .minimum
          (.extremum .minimum
            (.atom (.field
              (ordinaryPath ["Order", "Sections"] "OuterAmount")))
            (.atom (.field
              (ordinaryPath ["Order", "Sections", "Items"]
                "InnerAmount"))))
        right := .literal { value := expected, authoredScale := 0 }
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  condition.core.iterationLegality.toOption

def plainStarProductCondition?
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let source ←
    (elaborateNumericProductAggregate ordinaryIterationModel
      ["Order", "Sections"] {
        left := deeperInnerAmountStar
        right := deeperInnerPriceStar
      }).toOption
  let comparison ← checkedOuterEntityComparison? {
    op
    left := .atom (.sumOfProducts source)
    right := .literal { value := expected, authoredScale := 0 }
  }
  (CheckedValidationCondition.fromOrderedNumeric comparison).toOption

def plainStarProductLegality?
    (op : NumericValidationOp) (expected : Rat) :
    Option ValidationCondition.IterationLegality := do
  let condition ← plainStarProductCondition? op expected
  condition.core.iterationLegality.toOption

def guardedPlainStarProductRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let outer ←
    (CheckedValidationCondition.fromRepeatableFieldPresence
      ordinaryIterationModel ["Order", "Sections"] .filled
      (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption
  let product ←
    plainStarProductCondition? (.ordinary .greater) 0
  let condition ← (outer.and product).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition
    outerAmount.id "guardedProduct" .error { parts := [] }).toOption

def outerWithInnerEntityComparison?
    (atom : OrderedNumericValidationAtom ordinaryIterationModel)
    (right : Rat) :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let outerField ← outerAmount.toNumberField?
  checkedOuterEntityComparison? {
    op := .ordinary .equal
    left := .binary .add
      (.atom (.ordinary (.field outerField)))
      (.atom atom)
    right := .literal { value := right, authoredScale := 0 }
  }

def outerWithInnerFirstFilledComparison? :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let source ← deeperInnerNumberSource?
  outerWithInnerEntityComparison? (.firstFilled source) 5

def outerWithInnerValueCountComparison? :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let source ← deeperInnerNumberSource?
  outerWithInnerEntityComparison? (.valueCount 4 source) 2

def outerWithFilteredInnerFirstFilledComparison? :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let source ← deeperInnerNumberSource? true
  outerWithInnerEntityComparison? (.firstFilled source) 5

def outerWithFilteredInnerValueCountComparison? :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let source ← deeperInnerNumberSource? true
  outerWithInnerEntityComparison? (.valueCount 4 source) 3

def outerWithInnerEntityRule?
    (comparison :
      Option (CheckedOrderedNumericComparison ordinaryIterationModel))
    (errorCode : String) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let numeric ← comparison
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition outerAmount.id
    errorCode .error { parts := [] }).toOption

def outerWithInnerFirstFilledRule? :=
  outerWithInnerEntityRule? outerWithInnerFirstFilledComparison?
    "outerWithInnerFirstFilled"

def outerWithInnerValueCountRule? :=
  outerWithInnerEntityRule? outerWithInnerValueCountComparison?
    "outerWithInnerValueCount"

def outerWithFilteredInnerFirstFilledRule? :=
  outerWithInnerEntityRule? outerWithFilteredInnerFirstFilledComparison?
    "outerWithFilteredInnerFirstFilled"

def outerWithFilteredInnerValueCountRule? :=
  outerWithInnerEntityRule? outerWithFilteredInnerValueCountComparison?
    "outerWithFilteredInnerValueCount"

/- Nested compatible ordinary references derive the deepest scope from the checked tree; the declaring group and error-field argument cannot override it. -/

end A12Kernel.Conformance.ValidationRule.OrdinarySupport
