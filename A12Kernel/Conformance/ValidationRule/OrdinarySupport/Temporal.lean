import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Core

/-! # Shared ordinary repeatable temporal fixtures -/

namespace A12Kernel.Conformance.ValidationRule.OrdinarySupport

open A12Kernel

def repeatableTemporalPartCondition?
    (field : String) (part : TemporalNumericPart)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let component : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.temporalFieldPart
      (ordinaryPath ["Order", "Sections", "Items"] field) part)
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := if literalOnLeft then literal else component
        right := if literalOnLeft then component else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

def repeatableTemporalPartLegality?
    (field : String) (part : TemporalNumericPart)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    repeatableTemporalPartCondition? field part op expected literalOnLeft
  condition.core.iterationLegality.toOption

def repeatableTemporalPartRule?
    (field : String) (part : TemporalNumericPart)
    (op : NumericValidationOp) (expected : Rat) (target : FieldId) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← repeatableTemporalPartCondition? field part op expected
  (assembleResolvedValidationRule ordinaryIterationModel condition target
    "repeatableTemporalPart" .error { parts := [] }).toOption

def repeatableDateDifferenceConditionWith?
    (unit : DateDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let difference : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.dateDifference unit left right)
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := if literalOnLeft then literal else difference
        right := if literalOnLeft then difference else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

def repeatableDateDifferenceCondition?
    (unit : DateDifferenceUnit) (left right : String)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  repeatableDateDifferenceConditionWith? unit
    (.field (ordinaryPath ["Order", "Sections", "Items"] left))
    (.field (ordinaryPath ["Order", "Sections", "Items"] right))
    op expected literalOnLeft

def repeatableDateDifferenceLegality?
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ← repeatableDateDifferenceCondition? .months
    "InnerDate" "InnerEarlierDate" op expected literalOnLeft
  condition.core.iterationLegality.toOption

def dateDifferenceConditionLegality?
    (condition : Option
      (CheckedValidationCondition ordinaryIterationModel)) :
    Option ValidationCondition.IterationLegality := do
  let checked ← condition
  checked.core.iterationLegality.toOption

def repeatableDayDifferenceCondition?
    (left right : SurfaceDateDifferenceOperand)
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let difference : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.dayDifference left right)
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := difference
        right := .literal { value := expected, authoredScale := 0 }
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

def repeatableDayDifferenceRule?
    (left right : SurfaceDateDifferenceOperand)
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← repeatableDayDifferenceCondition? left right op expected
  (assembleResolvedValidationRule ordinaryIterationModel condition innerDate.id
    "repeatableDayDifference" .error { parts := [] }).toOption

def repeatableDateTimeDifferenceCondition?
    (unit : DateTimeDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand)
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let difference : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.dateTimeDifference unit left right)
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := difference
        right := .literal { value := expected, authoredScale := 0 }
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

def repeatableDateTimeDifferenceRule?
    (unit : DateTimeDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand)
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ←
    repeatableDateTimeDifferenceCondition? unit left right op expected
  (assembleResolvedValidationRule ordinaryIterationModel condition
    innerDateTime.id "repeatableDateTimeDifference" .error
    { parts := [] }).toOption

def repeatableDateDifferenceRuleWith?
    (unit : DateDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand)
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← repeatableDateDifferenceConditionWith?
    unit left right op expected
  (assembleResolvedValidationRule ordinaryIterationModel condition innerDate.id
    "repeatableDateDifference" .error { parts := [] }).toOption

def repeatableDateDifferenceRule?
    (unit : DateDifferenceUnit) (left right : String)
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) :=
  repeatableDateDifferenceRuleWith? unit
    (.field (ordinaryPath ["Order", "Sections", "Items"] left))
    (.field (ordinaryPath ["Order", "Sections", "Items"] right))
    op expected

end A12Kernel.Conformance.ValidationRule.OrdinarySupport
