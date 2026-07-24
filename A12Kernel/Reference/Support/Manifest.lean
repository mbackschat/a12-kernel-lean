import A12Kernel.Reference.Support.Diagnostics
import Lean.Data.Json.FromToJson.Basic

/-! # Generated public support manifest -/

namespace A12Kernel.Reference.Support

open Lean

structure ComparisonCapability where
  fieldKind : FieldKindTag
  literalKind : LiteralKindTag
  operators : List ComparisonOperator
  deriving Repr, DecidableEq

def comparisonMatrix : List ComparisonCapability := [
  { fieldKind := .number, literalKind := .number,
    operators := ComparisonOperator.supported },
  { fieldKind := .boolean, literalKind := .boolean,
    operators := ComparisonOperator.supported },
  { fieldKind := .confirm, literalKind := .booleanTrue,
    operators := ComparisonOperator.supported }]

private def tagArray {α : Type} (values : List α) (tag : α → String) : Json :=
  toJson (values.map tag)

private def comparisonCapabilityJson (capability : ComparisonCapability) : Json :=
  Json.mkObj [
    ("fieldKind", toJson capability.fieldKind.tag),
    ("literalKind", toJson capability.literalKind.tag),
    ("operators", tagArray capability.operators ComparisonOperator.tag)]

private def publicLimitsJson (limits : PublicLimits) : Json :=
  Json.mkObj [
    ("inputBytes", toJson limits.inputBytes),
    ("jsonNesting", toJson limits.jsonNesting),
    ("jsonNumberCharacters", toJson limits.jsonNumberCharacters),
    ("naturalNumberMaximum", toJson limits.naturalNumberMaximum),
    ("fields", toJson limits.fields),
    ("cells", toJson limits.cells),
    ("candidates", toJson limits.candidates),
    ("repeatableGroups", toJson limits.repeatableGroups),
    ("conditionDepth", toJson limits.conditionDepth),
    ("conditionNodes", toJson limits.conditionNodes),
    ("pathSegments", toJson limits.pathSegments),
    ("repeatableScopeLevels", toJson limits.repeatableScopeLevels),
    ("segmentBytes", toJson limits.segmentBytes),
    ("decimalCharacters", toJson limits.decimalCharacters)]

private def diagnosticCodeJson (code : DiagnosticCode) : Json :=
  Json.mkObj [
    ("category", toJson code.category.tag),
    ("code", toJson code.tag)]

private def flatAcceptedManifest : Json :=
  Json.mkObj [
    ("fieldKinds", tagArray FieldKindTag.all FieldKindTag.tag),
    ("conditionForms", tagArray ConditionFormTag.all ConditionFormTag.tag),
    ("comparisonMatrix", Json.arr (comparisonMatrix.map comparisonCapabilityJson).toArray),
    ("pathForms", tagArray PathFormTag.all PathFormTag.tag),
    ("referencedScopes", tagArray ReferencedScopeTag.all ReferencedScopeTag.tag),
    ("explicitRawCellForms", tagArray RawCellFormTag.all RawCellFormTag.tag),
    ("emptyCellEncoding", toJson "sparseOmission"),
    ("rejectedCauses", tagArray RejectedCauseTag.all RejectedCauseTag.tag),
    ("rowGate", toJson "explicitHasContent"),
    ("verdicts", tagArray VerdictTag.all VerdictTag.tag),
    ("externalEvidenceBoundary", Json.mkObj [
      ("observable", toJson "focusedRuleMessagePresenceAndPolarity"),
      ("nonFiringVerdictDistinction", toJson "notFiredVersusUnknownLeanAccountOnly"),
      ("claimScope", toJson "finiteRetainedCasesOnly"),
      ("suiteId", toJson "flat-validation-empty-logic-v2"),
      ("retainedRuntimeCaseCount", toJson 9),
      ("retainedStaticCaseCount", toJson 0),
      ("generalAcceptedInputs", toJson "leanAccountExternalEvidencePending")])]

private def correlationAcceptedManifest : Json :=
  Json.mkObj [
    ("fieldKinds", toJson ["number"]),
    ("havingForms", tagArray CorrelatedHavingFormTag.all CorrelatedHavingFormTag.tag),
    ("comparisonOperators",
      tagArray ComparisonOperator.correlationSupported ComparisonOperator.tag),
    ("origins", tagArray HavingOriginTag.all HavingOriginTag.tag),
    ("fieldAndGroupPathForms",
      tagArray CorrelationPathFormTag.all CorrelationPathFormTag.tag),
    ("childRelativeGroupSegments", toJson 1),
    ("starPathForms",
      tagArray CorrelationStarPathFormTag.all CorrelationStarPathFormTag.tag),
    ("directChildRelativeStarPrefixSegments", toJson 0),
    ("starParentNavigation", toJson "rejected"),
    ("selectedGroupCount", toJson 1),
    ("selectedFieldPlacement", toJson "directChildOfSelectedGroup"),
    ("modelMayDeclareSiblingRepeatableGroups", toJson true),
    ("starCount", toJson 1),
    ("wholeRuleInvariants", toJson [
      "havingContainsInnerAndOuter",
      "errorFieldEqualsGuardField",
      "allRuleFieldsUseSelectedGroupAndSingletonScope"]),
    ("comparisonScalePolicy", Json.mkObj [
      ("equal", toJson "declaredScalesEqual"),
      ("notEqual", toJson "declaredScalesEqual"),
      ("less", toJson "declaredScalesMayDiffer")]),
    ("consumer", toJson "selectedNumberPresence"),
    ("outerGuard", toJson "numberFieldFilled"),
    ("candidateEncoding", toJson "nonEmptyContiguousOneBasedRowIds"),
    ("explicitRawCellForms",
      tagArray CorrelationCellFormTag.all CorrelationCellFormTag.tag),
    ("numberTransport", toJson "canonicalExactDecimal"),
    ("emptyCellEncoding", toJson "sparseRowFieldOmission"),
    ("result", toJson "orderedFiringRows"),
    ("externalEvidenceBoundary", Json.mkObj [
      ("runtimeNumberCells", toJson "retainedCasesUseNonNegativeIntegers"),
      ("candidateRows", toJson "retainedCasesUseContiguousOneBasedRows"),
      ("observable", toJson "firingRowsOnly"),
      ("claimScope", toJson "finiteRetainedCasesOnly"),
      ("suiteId", toJson "single-group-correlation-v2"),
      ("retainedRuntimeCaseCount", toJson 12),
      ("retainedStaticCaseCount", toJson 4),
      ("generalAcceptedInputs", toJson "leanAccountExternalEvidencePending")])]

private def operationManifest : Operation → Json
  | .flatValidationEvaluateFull =>
      Json.mkObj [
        ("operation", toJson Operation.flatValidationEvaluateFull.tag),
        ("accepted", flatAcceptedManifest),
        ("recognizedButUnsupportedComparisonOperators",
          tagArray ComparisonOperator.unsupported ComparisonOperator.tag)]
  | .singleGroupCorrelationFiringRows =>
      Json.mkObj [
        ("operation", toJson Operation.singleGroupCorrelationFiringRows.tag),
        ("accepted", correlationAcceptedManifest),
        ("recognizedButUnsupportedComparisonOperators",
          tagArray ComparisonOperator.correlationUnsupported ComparisonOperator.tag)]

def supportManifest : Json :=
  Json.mkObj [
    ("manifestSchemaVersion", toJson manifestSchemaVersion),
    ("referenceSemanticsVersion", toJson referenceSemanticsVersion),
    ("protocolVersion", toJson protocolVersion),
    ("kernelBehaviorVersion", toJson kernelBehaviorVersion),
    ("supportPolicy", toJson supportPolicy),
    ("operations", Json.arr (Operation.all.map operationManifest).toArray),
    ("diagnostics", Json.arr (DiagnosticCode.all.map diagnosticCodeJson).toArray),
    ("limits", publicLimitsJson publicLimits),
    ("knownExclusions", tagArray KnownExclusion.all KnownExclusion.tag)]

end A12Kernel.Reference.Support
