import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.ValidationRule

/-! # Shared ordinary repeatable scalar and temporal fixtures -/

namespace A12Kernel.Conformance.ValidationRule.OrdinarySupport

open A12Kernel

def dateTimeComponents : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := true, minute := true, second := true }

def defaultWorld : World :=
  { now := { epochMillis := 0 } }

def outerAmount : FlatFieldDecl :=
  { id := 30
    groupPath := ["Order", "Sections"]
    name := "OuterAmount"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10] }

def innerAmount : FlatFieldDecl :=
  { id := 31
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerAmount"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10, 20] }

def innerPrice : FlatFieldDecl :=
  { id := 33
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerPrice"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10, 20] }

def baseAmount : FlatFieldDecl :=
  { id := 34
    groupPath := ["Order"]
    name := "BaseAmount"
    policy := { kind := .number { scale := 0, signed := true } } }

def innerToken : FlatFieldDecl :=
  { id := 35
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerToken"
    policy := { kind := .string }
    repeatableScope := [10, 20] }

def baseToken : FlatFieldDecl :=
  { id := 36
    groupPath := ["Order"]
    name := "BaseToken"
    policy := { kind := .string } }

def innerNumericCode : FlatFieldDecl :=
  { id := 37
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerNumericCode"
    policy := { kind := .string }
    stringPatternSource := some "[0-9]+"
    stringPolicy := { maxLength := some 15 }
    repeatableScope := [10, 20] }

def innerNumericChoice : FlatFieldDecl :=
  { id := 38
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerNumericChoice"
    policy := { kind := .enumeration }
    enumeration := some {
      storedTokens := ["1.50", "2"]
      categories := [{ name := "Factor", tokens := ["15", "20"] }] }
    repeatableScope := [10, 20] }

def innerDate : FlatFieldDecl :=
  { id := 39
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerDate"
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    repeatableScope := [10, 20] }

def innerTime : FlatFieldDecl :=
  { id := 40
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerTime"
    policy := { kind := .temporal .time {
      year := false, month := false, day := false,
      hour := true, minute := true, second := true } }
    repeatableScope := [10, 20] }

def innerDateTime : FlatFieldDecl :=
  { id := 41
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerDateTime"
    policy := { kind := .temporal .dateTime dateTimeComponents }
    repeatableScope := [10, 20] }

def innerEarlierDate : FlatFieldDecl :=
  { id := 42
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerEarlierDate"
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    repeatableScope := [10, 20] }

def outerDate : FlatFieldDecl :=
  { id := 43
    groupPath := ["Order", "Sections"]
    name := "OuterDate"
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    repeatableScope := [10] }

def siblingDate : FlatFieldDecl :=
  { id := 44
    groupPath := ["Order", "Sections", "Notes"]
    name := "SiblingDate"
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    repeatableScope := [10, 30] }

def innerEarlierDateTime : FlatFieldDecl :=
  { id := 45
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerEarlierDateTime"
    policy := { kind := .temporal .dateTime dateTimeComponents }
    repeatableScope := [10, 20] }

def sectionDetail : FlatFieldDecl :=
  { id := 32
    groupPath := ["Order", "Sections", "Details"]
    name := "SectionDetail"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10] }

def ordinaryIterationModel : FlatModel :=
  { fields := [outerAmount, innerAmount, sectionDetail, innerPrice, baseAmount,
      innerToken, baseToken, innerNumericCode, innerNumericChoice, innerDate,
      innerTime, innerDateTime, innerEarlierDate, outerDate, siblingDate,
      innerEarlierDateTime]
    baseYear := some 2020
    repeatableGroups := [
      { level := 10, path := ["Order", "Sections"], repeatability := some 2 },
      { level := 20, path := ["Order", "Sections", "Items"],
        repeatability := some 2 },
      { level := 30, path := ["Order", "Sections", "Notes"],
        repeatability := some 2 }] }

def ordinaryPath (groups : List String) (field : String) :
    SurfaceFieldPath :=
  { base := .absolute, groups, field }

def outerIterationCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order"] .filled
    (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption

def innerEmptyCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order"] .notFilled
    (ordinaryPath ["Order", "Sections", "Items"] "InnerAmount")).toOption

def innerGroupFilledCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromGroupPresence ordinaryIterationModel
    ["Order"] (.path {
      base := .absolute
      groups := ["Order", "Sections", "Items"]
    }) .filled).toOption

def nestedUnguardedCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let outer ← outerIterationCondition?
  let inner ← innerEmptyCondition?
  (outer.and inner).toOption

def ordinaryIterationCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let outer ←
    outerIterationCondition?
  let innerGroup ← innerGroupFilledCondition?
  let inner ← innerEmptyCondition?
  let guardedInner ← (innerGroup.and inner).toOption
  (outer.and guardedInner).toOption

def ordinaryIterationRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← ordinaryIterationCondition?
  (assembleResolvedValidationRule ordinaryIterationModel condition innerAmount.id
    "ordinaryIteration" .error { parts := [] }).toOption

def absoluteGroup (groups : GroupPath) : SurfaceGroupReference := .path { base := .absolute, groups }

def ordinaryGroupPresenceRule?
    (rowGroup : GroupPath) (reference : SurfaceGroupReference)
    (target : FlatFieldDecl) (errorCode : String) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ←
    (CheckedValidationCondition.fromGroupPresence ordinaryIterationModel
      rowGroup reference .filled).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition target.id
    errorCode .error { parts := [] }).toOption

def outerGroupPathRule? :=
  ordinaryGroupPresenceRule? ["Order"]
    (absoluteGroup ["Order", "Sections"]) outerAmount "outerGroupPath"

def outerRuleGroupRule? :=
  ordinaryGroupPresenceRule? ["Order", "Sections"]
    (.ruleGroup false) outerAmount "outerRuleGroup"

def detailGroupPathRule? :=
  ordinaryGroupPresenceRule? ["Order"]
    (absoluteGroup ["Order", "Sections", "Details"])
    sectionDetail "detailGroupPath"

def ordinaryRepeatableNumericRuleAt?
    (groups : List String) (field : String)
    (target : FieldId) (errorCode : String) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      groups {
        op := .ordinary .greaterEqual
        left := .binary .add
          (.atom (.field
            (ordinaryPath groups field)))
          (.literal { value := 1, authoredScale := 0 })
        right := .literal { value := 1, authoredScale := 0 }
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition target
    errorCode .error { parts := [] }).toOption

def ordinaryRepeatableNumericRule? :=
  ordinaryRepeatableNumericRuleAt? ["Order", "Sections"]
    "OuterAmount" outerAmount.id "ordinaryNumeric"

def nestedRepeatableNumericRule? :=
  ordinaryRepeatableNumericRuleAt? ["Order", "Sections", "Items"]
    "InnerAmount" innerAmount.id "nestedNumeric"

def ancestorCurrentNumericRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op := .ordinary .greater
        left := .binary .add
          (.atom (.field
            (ordinaryPath ["Order", "Sections"] "OuterAmount")))
          (.atom (.field
            (ordinaryPath ["Order", "Sections", "Items"] "InnerAmount")))
        right := .literal { value := 4, authoredScale := 0 }
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition innerAmount.id
    "ancestorCurrentNumeric" .error { parts := [] }).toOption

def directRepeatableNumericLiteralCondition?
    (op : NumericValidationOp) (literalValue : DecodedNumericLiteral)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let field : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.field
      (ordinaryPath ["Order", "Sections"] "OuterAmount"))
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal literalValue
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections"] {
        op
        left := if literalOnLeft then literal else field
        right := if literalOnLeft then field else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

def directRepeatableNumericCondition?
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  directRepeatableNumericLiteralCondition? op
    { value := expected, authoredScale := 0 } literalOnLeft

def directRepeatableNumericLiteralLegality?
    (op : NumericValidationOp) (literal : DecodedNumericLiteral)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    directRepeatableNumericLiteralCondition? op literal literalOnLeft
  condition.core.iterationLegality.toOption

def directRepeatableNumericLegality?
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    directRepeatableNumericCondition? op expected literalOnLeft
  condition.core.iterationLegality.toOption

def repeatableStringLengthCondition?
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let length : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.stringLength
      (ordinaryPath ["Order", "Sections", "Items"] "InnerToken"))
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := if literalOnLeft then literal else length
        right := if literalOnLeft then length else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

def repeatableStringLengthLegality?
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    repeatableStringLengthCondition? op expected literalOnLeft
  condition.core.iterationLegality.toOption

def repeatableStringLengthRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ←
    repeatableStringLengthCondition? (.ordinary .equal) 3
  (assembleResolvedValidationRule ordinaryIterationModel condition innerToken.id
    "repeatableStringLength" .error { parts := [] }).toOption

def repeatableFieldValueAsNumberCondition?
    (source : SurfaceTextFieldOperand)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let converted : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.fieldValueAsNumber source)
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := if literalOnLeft then literal else converted
        right := if literalOnLeft then converted else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

def repeatableFieldValueAsNumberLegality?
    (source : SurfaceTextFieldOperand)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    repeatableFieldValueAsNumberCondition? source op expected literalOnLeft
  condition.core.iterationLegality.toOption

def repeatableNumericCode : SurfaceTextFieldOperand :=
  .direct
    (ordinaryPath ["Order", "Sections", "Items"] "InnerNumericCode")

def repeatableNumericFactor : SurfaceTextFieldOperand :=
  .category
    (ordinaryPath ["Order", "Sections", "Items"] "InnerNumericChoice")
    "Factor"

def repeatableFieldValueAsNumberRule?
    (source : SurfaceTextFieldOperand) (expected : Rat) (target : FieldId) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ←
    repeatableFieldValueAsNumberCondition? source (.ordinary .equal) expected
  (assembleResolvedValidationRule ordinaryIterationModel condition target
    "repeatableFieldValueAsNumber" .error { parts := [] }).toOption

def repeatableStringRangeCondition?
    (op : NumericValidationOp) (expected : Rat)
    (start : Nat := 2) (finish : Nat := 3)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let range : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.stringRange
      (ordinaryPath ["Order", "Sections", "Items"] "InnerToken")
      start finish)
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := if literalOnLeft then literal else range
        right := if literalOnLeft then range else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

def repeatableStringRangeLegality?
    (op : NumericValidationOp) (expected : Rat)
    (start : Nat := 2) (finish : Nat := 3)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    repeatableStringRangeCondition? op expected start finish literalOnLeft
  condition.core.iterationLegality.toOption

def repeatableStringRangeRule?
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← repeatableStringRangeCondition? op expected
  (assembleResolvedValidationRule ordinaryIterationModel condition innerToken.id
    "repeatableStringRange" .error { parts := [] }).toOption

def compositeRepeatableNumericLegality?
    (op : NumericValidationOp) (expected : Rat) :
    Option ValidationCondition.IterationLegality := do
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections"] {
        op
        left := .binary .add
          (.atom (.field
            (ordinaryPath ["Order", "Sections"] "OuterAmount")))
          (.literal { value := 0, authoredScale := 0 })
        right := .literal { value := expected, authoredScale := 0 }
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  condition.core.iterationLegality.toOption

def wrappedRepeatableNumericLegality?
    (wrap : AuthoredNumericExpr SurfaceNumericAtom →
      AuthoredNumericExpr SurfaceNumericAtom)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let wrapped := wrap (.atom (.field
    (ordinaryPath ["Order", "Sections"] "OuterAmount")))
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections"] {
        op
        left := if literalOnLeft then literal else wrapped
        right := if literalOnLeft then wrapped else literal
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  condition.core.iterationLegality.toOption

end A12Kernel.Conformance.ValidationRule.OrdinarySupport
