import A12Kernel.Reference.Support.Vocabulary

/-! # Protocol diagnostic and exclusion vocabulary -/

namespace A12Kernel.Reference.Support

inductive DiagnosticCode where
  | unsupportedVersion
  | kernelBehaviorVersionMismatch
  | unsupportedOperation
  | invalidShape
  | resourceLimit
  | invalidDecimal
  | invalidJsonNumber
  | duplicateCellId
  | duplicateCellAddress
  | cellRowNotCandidate
  | zeroCandidate
  | duplicateCandidate
  | invalidCandidateSequence
  | cellOutsideGroup
  | undeclaredCellId
  | invalidJson
  | duplicateMember
  | pathBase
  | pathForm
  | literalKind
  | conditionForm
  | havingForm
  | havingOrigin
  | uncorrelatedHaving
  | operator
  | fieldKind
  | cellState
  | rejectedCause
  | repeatableReference
  | repeatableCell
  | invalidPath
  | duplicateFieldId
  | duplicateEntityPath
  | invalidRepeatableGroupPath
  | duplicateRepeatableGroupPath
  | duplicateRepeatableLevel
  | hierarchyCollision
  | repeatableScopeMismatch
  | unknownRepeatableGroup
  | unknownFieldId
  | invalidRuleGroup
  | invalidReference
  | aboveRoot
  | unknownField
  | ambiguousField
  | shortNameNotUnique
  | literalKindMismatch
  | illegalConfirmLiteral
  | invalidGroupReference
  | fieldKindMismatch
  | fieldOutsideGroup
  | fieldScopeMismatch
  | repetitionGroupMismatch
  | equalityScaleMismatch
  | missingInner
  | errorGuardMismatch
  deriving Repr, DecidableEq, BEq

namespace DiagnosticCode

def all : List DiagnosticCode := [
  .unsupportedVersion, .kernelBehaviorVersionMismatch, .unsupportedOperation,
  .invalidShape, .resourceLimit, .invalidDecimal, .invalidJsonNumber,
  .duplicateCellId, .duplicateCellAddress, .cellRowNotCandidate, .zeroCandidate,
  .duplicateCandidate, .invalidCandidateSequence, .cellOutsideGroup, .undeclaredCellId, .invalidJson,
  .duplicateMember,
  .pathBase, .pathForm, .literalKind, .conditionForm, .havingForm, .havingOrigin,
  .uncorrelatedHaving, .operator, .fieldKind,
  .cellState, .rejectedCause, .repeatableReference, .repeatableCell,
  .invalidPath, .duplicateFieldId, .duplicateEntityPath, .invalidRepeatableGroupPath,
  .duplicateRepeatableGroupPath, .duplicateRepeatableLevel, .hierarchyCollision,
  .repeatableScopeMismatch, .unknownRepeatableGroup, .unknownFieldId,
  .invalidRuleGroup, .invalidReference, .aboveRoot, .unknownField, .ambiguousField,
  .shortNameNotUnique, .literalKindMismatch, .illegalConfirmLiteral,
  .invalidGroupReference, .fieldKindMismatch, .fieldOutsideGroup,
  .fieldScopeMismatch, .repetitionGroupMismatch, .equalityScaleMismatch,
  .missingInner, .errorGuardMismatch]

def tag : DiagnosticCode → String
  | .unsupportedVersion => "unsupportedVersion"
  | .kernelBehaviorVersionMismatch => "kernelBehaviorVersionMismatch"
  | .unsupportedOperation => "unsupportedOperation"
  | .invalidShape => "invalidShape"
  | .resourceLimit => "resourceLimit"
  | .invalidDecimal => "invalidDecimal"
  | .invalidJsonNumber => "invalidJsonNumber"
  | .duplicateCellId => "duplicateCellId"
  | .duplicateCellAddress => "duplicateCellAddress"
  | .cellRowNotCandidate => "cellRowNotCandidate"
  | .zeroCandidate => "zeroCandidate"
  | .duplicateCandidate => "duplicateCandidate"
  | .invalidCandidateSequence => "invalidCandidateSequence"
  | .cellOutsideGroup => "cellOutsideGroup"
  | .undeclaredCellId => "undeclaredCellId"
  | .invalidJson => "invalidJson"
  | .duplicateMember => "duplicateMember"
  | .pathBase => "pathBase"
  | .pathForm => "pathForm"
  | .literalKind => "literalKind"
  | .conditionForm => "conditionForm"
  | .havingForm => "havingForm"
  | .havingOrigin => "havingOrigin"
  | .uncorrelatedHaving => "uncorrelatedHaving"
  | .operator => "operator"
  | .fieldKind => "fieldKind"
  | .cellState => "cellState"
  | .rejectedCause => "rejectedCause"
  | .repeatableReference => "repeatableReference"
  | .repeatableCell => "repeatableCell"
  | .invalidPath => "invalidPath"
  | .duplicateFieldId => "duplicateFieldId"
  | .duplicateEntityPath => "duplicateEntityPath"
  | .invalidRepeatableGroupPath => "invalidRepeatableGroupPath"
  | .duplicateRepeatableGroupPath => "duplicateRepeatableGroupPath"
  | .duplicateRepeatableLevel => "duplicateRepeatableLevel"
  | .hierarchyCollision => "hierarchyCollision"
  | .repeatableScopeMismatch => "repeatableScopeMismatch"
  | .unknownRepeatableGroup => "unknownRepeatableGroup"
  | .unknownFieldId => "unknownFieldId"
  | .invalidRuleGroup => "invalidRuleGroup"
  | .invalidReference => "invalidReference"
  | .aboveRoot => "aboveRoot"
  | .unknownField => "unknownField"
  | .ambiguousField => "ambiguousField"
  | .shortNameNotUnique => "shortNameNotUnique"
  | .literalKindMismatch => "literalKindMismatch"
  | .illegalConfirmLiteral => "illegalConfirmLiteral"
  | .invalidGroupReference => "invalidGroupReference"
  | .fieldKindMismatch => "fieldKindMismatch"
  | .fieldOutsideGroup => "fieldOutsideGroup"
  | .fieldScopeMismatch => "fieldScopeMismatch"
  | .repetitionGroupMismatch => "repetitionGroupMismatch"
  | .equalityScaleMismatch => "equalityScaleMismatch"
  | .missingInner => "missingInner"
  | .errorGuardMismatch => "errorGuardMismatch"

def category : DiagnosticCode → DiagnosticCategory
  | .unsupportedVersion | .kernelBehaviorVersionMismatch | .unsupportedOperation => .protocol
  | .invalidShape | .resourceLimit | .invalidDecimal | .invalidJsonNumber |
      .duplicateCellId | .duplicateCellAddress | .cellRowNotCandidate | .zeroCandidate |
      .duplicateCandidate | .invalidCandidateSequence | .cellOutsideGroup |
      .undeclaredCellId | .invalidJson |
      .duplicateMember => .input
  | .pathBase | .pathForm | .literalKind | .conditionForm | .havingForm |
      .havingOrigin | .uncorrelatedHaving | .operator | .fieldKind | .cellState |
      .rejectedCause | .repeatableReference | .repeatableCell => .unsupported
  | .invalidPath | .duplicateFieldId | .duplicateEntityPath |
      .invalidRepeatableGroupPath | .duplicateRepeatableGroupPath |
      .duplicateRepeatableLevel | .hierarchyCollision | .repeatableScopeMismatch => .model
  | .unknownRepeatableGroup | .unknownFieldId | .invalidRuleGroup | .invalidReference |
      .aboveRoot | .unknownField | .ambiguousField | .shortNameNotUnique |
      .literalKindMismatch | .illegalConfirmLiteral | .invalidGroupReference |
      .fieldKindMismatch | .fieldOutsideGroup | .fieldScopeMismatch |
      .repetitionGroupMismatch | .equalityScaleMismatch | .missingInner |
      .errorGuardMismatch => .elaboration

end DiagnosticCode

inductive KnownExclusion where
  | concreteDsl
  | generalDmJson
  | stringDateTimeEnumeration
  | generalOrderingAndArithmetic
  | generalRepeatableEvaluation
  | nestedOrMultipleStars
  | crossGroupCorrelation
  | generalCorrelationConsumers
  | filteredResultPolarity
  | computation
  | partialValidation
  | messageConstruction
  deriving Repr, DecidableEq, BEq

namespace KnownExclusion

def all : List KnownExclusion :=
  [.concreteDsl, .generalDmJson, .stringDateTimeEnumeration, .generalOrderingAndArithmetic,
    .generalRepeatableEvaluation, .nestedOrMultipleStars, .crossGroupCorrelation,
    .generalCorrelationConsumers, .filteredResultPolarity, .computation,
    .partialValidation, .messageConstruction]

def tag : KnownExclusion → String
  | .concreteDsl => "concreteDsl"
  | .generalDmJson => "generalDmJson"
  | .stringDateTimeEnumeration => "stringDateTimeEnumeration"
  | .generalOrderingAndArithmetic => "generalOrderingAndArithmetic"
  | .generalRepeatableEvaluation => "generalRepeatableEvaluation"
  | .nestedOrMultipleStars => "nestedOrMultipleStars"
  | .crossGroupCorrelation => "crossGroupCorrelation"
  | .generalCorrelationConsumers => "generalCorrelationConsumers"
  | .filteredResultPolarity => "filteredResultPolarity"
  | .computation => "computation"
  | .partialValidation => "partialValidation"
  | .messageConstruction => "messageConstruction"

def fromTag? : String → Option KnownExclusion
  | "concreteDsl" => some .concreteDsl
  | "generalDmJson" => some .generalDmJson
  | "stringDateTimeEnumeration" => some .stringDateTimeEnumeration
  | "generalOrderingAndArithmetic" => some .generalOrderingAndArithmetic
  | "generalRepeatableEvaluation" => some .generalRepeatableEvaluation
  | "nestedOrMultipleStars" => some .nestedOrMultipleStars
  | "crossGroupCorrelation" => some .crossGroupCorrelation
  | "generalCorrelationConsumers" => some .generalCorrelationConsumers
  | "filteredResultPolarity" => some .filteredResultPolarity
  | "computation" => some .computation
  | "partialValidation" => some .partialValidation
  | "messageConstruction" => some .messageConstruction
  | _ => none

def tagTable : List String := all.map tag

end KnownExclusion

end A12Kernel.Reference.Support
