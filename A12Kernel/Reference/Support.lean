import A12Kernel.Basic
import A12Kernel.Elaboration.Flat
import A12Kernel.Reference.StrictJson
import Lean.Data.Json.FromToJson.Basic

/-! # A12Kernel.Reference.Support — protocol-v1 support metadata

This module is the pure source of the public support manifest. Wire vocabulary is represented by finite enums, and the manifest is generated from their exhaustive tag tables rather than from a second hand-maintained JSON description.
-/

namespace A12Kernel.Reference.Support

open Lean

def manifestSchemaVersion : Nat := 2

def referenceSemanticsVersion : String := "0.3.0"

def protocolVersion : Nat := 1

def kernelBehaviorVersion : String := A12Kernel.kernelVersion

inductive Operation where
  | flatValidationEvaluateFull
  | singleGroupCorrelationFiringRows
  deriving Repr, DecidableEq, BEq

namespace Operation

def all : List Operation := [.flatValidationEvaluateFull, .singleGroupCorrelationFiringRows]

def tag : Operation → String
  | .flatValidationEvaluateFull => "flatValidation.evaluateFull"
  | .singleGroupCorrelationFiringRows => "singleGroupCorrelation.firingRows"

def fromTag? : String → Option Operation
  | "flatValidation.evaluateFull" => some .flatValidationEvaluateFull
  | "singleGroupCorrelation.firingRows" => some .singleGroupCorrelationFiringRows
  | _ => none

end Operation

def supportPolicy : String := "onlyListedCapabilities"

def maxInputBytes : Nat := 1048576

def maxJsonNesting : Nat := StrictJson.maxNesting

def maxJsonNumberCharacters : Nat := StrictJson.maxNumberCharacters

def maxNaturalNumber : Nat := 9007199254740991

def maxFields : Nat := 1024

def maxCells : Nat := 1024

def maxCandidates : Nat := 1024

def maxRepeatableGroups : Nat := 128

def maxConditionDepth : Nat := 64

def maxConditionNodes : Nat := 4096

def maxPathSegments : Nat := 64

def maxRepeatableScopeLevels : Nat := 64

def maxSegmentBytes : Nat := 256

def maxDecimalCharacters : Nat := 256

structure PublicLimits where
  inputBytes : Nat
  jsonNesting : Nat
  jsonNumberCharacters : Nat
  naturalNumberMaximum : Nat
  fields : Nat
  cells : Nat
  candidates : Nat
  repeatableGroups : Nat
  conditionDepth : Nat
  conditionNodes : Nat
  pathSegments : Nat
  repeatableScopeLevels : Nat
  segmentBytes : Nat
  decimalCharacters : Nat
  deriving Repr, DecidableEq

def publicLimits : PublicLimits := {
  inputBytes := maxInputBytes
  jsonNesting := maxJsonNesting
  jsonNumberCharacters := maxJsonNumberCharacters
  naturalNumberMaximum := maxNaturalNumber
  fields := maxFields
  cells := maxCells
  candidates := maxCandidates
  repeatableGroups := maxRepeatableGroups
  conditionDepth := maxConditionDepth
  conditionNodes := maxConditionNodes
  pathSegments := maxPathSegments
  repeatableScopeLevels := maxRepeatableScopeLevels
  segmentBytes := maxSegmentBytes
  decimalCharacters := maxDecimalCharacters }

inductive SupportStatus where
  | supported
  | unsupported
  deriving Repr, DecidableEq, BEq

inductive ComparisonOperator where
  | equal
  | notEqual
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving Repr, DecidableEq, BEq

namespace ComparisonOperator

def all : List ComparisonOperator :=
  [.equal, .notEqual, .less, .lessEqual, .greater, .greaterEqual]

def tag : ComparisonOperator → String
  | .equal => "equal"
  | .notEqual => "notEqual"
  | .less => "less"
  | .lessEqual => "lessEqual"
  | .greater => "greater"
  | .greaterEqual => "greaterEqual"

def fromTag? : String → Option ComparisonOperator
  | "equal" => some .equal
  | "notEqual" => some .notEqual
  | "less" => some .less
  | "lessEqual" => some .lessEqual
  | "greater" => some .greater
  | "greaterEqual" => some .greaterEqual
  | _ => none

def supportStatus : ComparisonOperator → SupportStatus
  | .equal | .notEqual => .supported
  | .less | .lessEqual | .greater | .greaterEqual => .unsupported

def isSupported (operator : ComparisonOperator) : Bool :=
  operator.supportStatus == .supported

def isCorrelationSupported : ComparisonOperator → Bool
  | .equal | .notEqual | .less => true
  | .lessEqual | .greater | .greaterEqual => false

def toSurface : ComparisonOperator → A12Kernel.SurfaceComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .less => .less
  | .lessEqual => .lessEqual
  | .greater => .greater
  | .greaterEqual => .greaterEqual

def ofSurface : A12Kernel.SurfaceComparisonOp → ComparisonOperator
  | .equal => .equal
  | .notEqual => .notEqual
  | .less => .less
  | .lessEqual => .lessEqual
  | .greater => .greater
  | .greaterEqual => .greaterEqual

def tagTable : List (String × SupportStatus) :=
  all.map fun operator => (operator.tag, operator.supportStatus)

def supported : List ComparisonOperator :=
  all.filter isSupported

def unsupported : List ComparisonOperator :=
  all.filter fun operator => !operator.isSupported

def correlationSupported : List ComparisonOperator :=
  all.filter isCorrelationSupported

def correlationUnsupported : List ComparisonOperator :=
  all.filter fun operator => !operator.isCorrelationSupported

end ComparisonOperator

inductive FieldKindTag where
  | number
  | boolean
  | confirm
  deriving Repr, DecidableEq, BEq

namespace FieldKindTag

def all : List FieldKindTag := [.number, .boolean, .confirm]

def tag : FieldKindTag → String
  | .number => "number"
  | .boolean => "boolean"
  | .confirm => "confirm"

def fromTag? : String → Option FieldKindTag
  | "number" => some .number
  | "boolean" => some .boolean
  | "confirm" => some .confirm
  | _ => none

def tagTable : List String := all.map tag

end FieldKindTag

inductive ConditionFormTag where
  | compare
  | fieldFilled
  | fieldNotFilled
  | and
  | or
  deriving Repr, DecidableEq, BEq

namespace ConditionFormTag

def all : List ConditionFormTag := [.compare, .fieldFilled, .fieldNotFilled, .and, .or]

def tag : ConditionFormTag → String
  | .compare => "compare"
  | .fieldFilled => "fieldFilled"
  | .fieldNotFilled => "fieldNotFilled"
  | .and => "and"
  | .or => "or"

def fromTag? : String → Option ConditionFormTag
  | "compare" => some .compare
  | "fieldFilled" => some .fieldFilled
  | "fieldNotFilled" => some .fieldNotFilled
  | "and" => some .and
  | "or" => some .or
  | _ => none

def tagTable : List String := all.map tag

end ConditionFormTag

inductive CorrelatedHavingFormTag where
  | compareNumbers
  | compareRepetitions
  | and
  deriving Repr, DecidableEq, BEq

namespace CorrelatedHavingFormTag

def all : List CorrelatedHavingFormTag := [.compareNumbers, .compareRepetitions, .and]

def tag : CorrelatedHavingFormTag → String
  | .compareNumbers => "compareNumbers"
  | .compareRepetitions => "compareRepetitions"
  | .and => "and"

def fromTag? : String → Option CorrelatedHavingFormTag
  | "compareNumbers" => some .compareNumbers
  | "compareRepetitions" => some .compareRepetitions
  | "and" => some .and
  | _ => none

end CorrelatedHavingFormTag

inductive HavingOriginTag where
  | inner
  | outer
  deriving Repr, DecidableEq, BEq

namespace HavingOriginTag

def all : List HavingOriginTag := [.inner, .outer]

def tag : HavingOriginTag → String
  | .inner => "inner"
  | .outer => "outer"

def fromTag? : String → Option HavingOriginTag
  | "inner" => some .inner
  | "outer" => some .outer
  | _ => none

end HavingOriginTag

inductive LiteralKindTag where
  | number
  | boolean
  | booleanTrue
  deriving Repr, DecidableEq, BEq

namespace LiteralKindTag

def all : List LiteralKindTag := [.number, .boolean, .booleanTrue]

def tag : LiteralKindTag → String
  | .number => "number"
  | .boolean => "boolean"
  | .booleanTrue => "booleanTrue"

def fromTag? : String → Option LiteralKindTag
  | "number" => some .number
  | "boolean" => some .boolean
  | "booleanTrue" => some .booleanTrue
  | _ => none

def tagTable : List String := all.map tag

end LiteralKindTag

inductive PathFormTag where
  | absolute
  | parentRelative
  | bare
  deriving Repr, DecidableEq, BEq

namespace PathFormTag

def all : List PathFormTag := [.absolute, .parentRelative, .bare]

def tag : PathFormTag → String
  | .absolute => "absolute"
  | .parentRelative => "parentRelative"
  | .bare => "bare"

def fromTag? : String → Option PathFormTag
  | "absolute" => some .absolute
  | "parentRelative" => some .parentRelative
  | "bare" => some .bare
  | _ => none

def tagTable : List String := all.map tag

def classify (base : A12Kernel.PathBase) (groups : List String) : Option PathFormTag :=
  match base, groups with
  | .absolute, _ => some .absolute
  | .relative 0, [] => some .bare
  | .relative 0, _ :: _ => none
  | .relative (_ + 1), _ => some .parentRelative

end PathFormTag

inductive CorrelationPathFormTag where
  | absolute
  | childRelative
  deriving Repr, DecidableEq, BEq

namespace CorrelationPathFormTag

def all : List CorrelationPathFormTag := [.absolute, .childRelative]

def tag : CorrelationPathFormTag → String
  | .absolute => "absolute"
  | .childRelative => "childRelative"

def fromTag? : String → Option CorrelationPathFormTag
  | "absolute" => some .absolute
  | "childRelative" => some .childRelative
  | _ => none

def classify (base : A12Kernel.PathBase) (groups : List String) :
    Option CorrelationPathFormTag :=
  match base, groups with
  | .absolute, _ => some .absolute
  | .relative 0, [_] => some .childRelative
  | .relative 0, [] | .relative 0, _ :: _ :: _ | .relative (_ + 1), _ => none

end CorrelationPathFormTag

inductive CorrelationStarPathFormTag where
  | absolute
  | directChildRelative
  deriving Repr, DecidableEq, BEq

namespace CorrelationStarPathFormTag

def all : List CorrelationStarPathFormTag := [.absolute, .directChildRelative]

def tag : CorrelationStarPathFormTag → String
  | .absolute => "absolute"
  | .directChildRelative => "directChildRelative"

def fromTag? : String → Option CorrelationStarPathFormTag
  | "absolute" => some .absolute
  | "directChildRelative" => some .directChildRelative
  | _ => none

def classify (base : A12Kernel.PathBase) (groupsBeforeStar : List String) :
    Option CorrelationStarPathFormTag :=
  match base, groupsBeforeStar with
  | .absolute, _ => some .absolute
  | .relative 0, [] => some .directChildRelative
  | .relative 0, _ :: _ | .relative (_ + 1), _ => none

end CorrelationStarPathFormTag

inductive ReferencedScopeTag where
  | nonrepeatable
  deriving Repr, DecidableEq, BEq

namespace ReferencedScopeTag

def all : List ReferencedScopeTag := [.nonrepeatable]

def tag : ReferencedScopeTag → String
  | .nonrepeatable => "nonrepeatable"

def fromTag? : String → Option ReferencedScopeTag
  | "nonrepeatable" => some .nonrepeatable
  | _ => none

def tagTable : List String := all.map tag

end ReferencedScopeTag

inductive RawCellFormTag where
  | parsedNumber
  | parsedBoolean
  | parsedConfirm
  | rejected
  deriving Repr, DecidableEq, BEq

namespace RawCellFormTag

def all : List RawCellFormTag :=
  [.parsedNumber, .parsedBoolean, .parsedConfirm, .rejected]

def tag : RawCellFormTag → String
  | .parsedNumber => "parsedNumber"
  | .parsedBoolean => "parsedBoolean"
  | .parsedConfirm => "parsedConfirm"
  | .rejected => "rejected"

def fromTag? : String → Option RawCellFormTag
  | "parsedNumber" => some .parsedNumber
  | "parsedBoolean" => some .parsedBoolean
  | "parsedConfirm" => some .parsedConfirm
  | "rejected" => some .rejected
  | _ => none

def tagTable : List String := all.map tag

end RawCellFormTag

inductive CorrelationCellFormTag where
  | parsedNumber
  | rejectedMalformed
  deriving Repr, DecidableEq, BEq

namespace CorrelationCellFormTag

def all : List CorrelationCellFormTag := [.parsedNumber, .rejectedMalformed]

def tag : CorrelationCellFormTag → String
  | .parsedNumber => "parsedNumber"
  | .rejectedMalformed => "rejected.malformed"

def fromTag? : String → Option CorrelationCellFormTag
  | "parsedNumber" => some .parsedNumber
  | "rejected.malformed" => some .rejectedMalformed
  | _ => none

end CorrelationCellFormTag

inductive RejectedCauseTag where
  | malformed
  | declaredConstraint
  | unsupportedCharacter
  | leadingOrTrailingSpace
  | customValidation
  deriving Repr, DecidableEq, BEq

namespace RejectedCauseTag

def all : List RejectedCauseTag :=
  [.malformed, .declaredConstraint, .unsupportedCharacter,
    .leadingOrTrailingSpace, .customValidation]

def tag : RejectedCauseTag → String
  | .malformed => "malformed"
  | .declaredConstraint => "declaredConstraint"
  | .unsupportedCharacter => "unsupportedCharacter"
  | .leadingOrTrailingSpace => "leadingOrTrailingSpace"
  | .customValidation => "customValidation"

def fromTag? : String → Option RejectedCauseTag
  | "malformed" => some .malformed
  | "declaredConstraint" => some .declaredConstraint
  | "unsupportedCharacter" => some .unsupportedCharacter
  | "leadingOrTrailingSpace" => some .leadingOrTrailingSpace
  | "customValidation" => some .customValidation
  | _ => none

def tagTable : List String := all.map tag

end RejectedCauseTag

namespace CorrelationCellFormTag

def classify (form : RawCellFormTag) (cause : Option RejectedCauseTag) :
    Option CorrelationCellFormTag :=
  match form, cause with
  | .parsedNumber, none => some .parsedNumber
  | .rejected, some .malformed => some .rejectedMalformed
  | _, _ => none

end CorrelationCellFormTag

inductive VerdictTag where
  | notFired
  | firedValue
  | firedOmission
  | unknown
  deriving Repr, DecidableEq, BEq

namespace VerdictTag

def all : List VerdictTag := [.notFired, .firedValue, .firedOmission, .unknown]

def tag : VerdictTag → String
  | .notFired => "notFired"
  | .firedValue => "fired.value"
  | .firedOmission => "fired.omission"
  | .unknown => "unknown"

def ofVerdict : A12Kernel.Verdict → VerdictTag
  | .notFired => .notFired
  | .fired .value => .firedValue
  | .fired .omission => .firedOmission
  | .unknown => .unknown

def fromTag? : String → Option VerdictTag
  | "notFired" => some .notFired
  | "fired.value" => some .firedValue
  | "fired.omission" => some .firedOmission
  | "unknown" => some .unknown
  | _ => none

def tagTable : List String := all.map tag

end VerdictTag

inductive DiagnosticCategory where
  | protocol
  | input
  | unsupported
  | model
  | elaboration
  deriving Repr, DecidableEq, BEq

namespace DiagnosticCategory

def all : List DiagnosticCategory := [.protocol, .input, .unsupported, .model, .elaboration]

def tag : DiagnosticCategory → String
  | .protocol => "protocol"
  | .input => "input"
  | .unsupported => "unsupported"
  | .model => "model"
  | .elaboration => "elaboration"

def fromTag? : String → Option DiagnosticCategory
  | "protocol" => some .protocol
  | "input" => some .input
  | "unsupported" => some .unsupported
  | "model" => some .model
  | "elaboration" => some .elaboration
  | _ => none

def tagTable : List String := all.map tag

end DiagnosticCategory

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

private def tagsRoundTrip [BEq α] (values : List α) (tag : α → String)
    (fromTag? : String → Option α) : Bool :=
  values.all fun value => fromTag? (tag value) == some value

example (operation : Operation) : Operation.all.contains operation = true := by
  cases operation <;> native_decide

example (operator : ComparisonOperator) : ComparisonOperator.all.contains operator = true := by
  cases operator <;> native_decide

example (kind : FieldKindTag) : FieldKindTag.all.contains kind = true := by
  cases kind <;> native_decide

example (form : ConditionFormTag) : ConditionFormTag.all.contains form = true := by
  cases form <;> native_decide

example (form : CorrelatedHavingFormTag) :
    CorrelatedHavingFormTag.all.contains form = true := by
  cases form <;> native_decide

example (origin : HavingOriginTag) : HavingOriginTag.all.contains origin = true := by
  cases origin <;> native_decide

example (kind : LiteralKindTag) : LiteralKindTag.all.contains kind = true := by
  cases kind <;> native_decide

example (form : PathFormTag) : PathFormTag.all.contains form = true := by
  cases form <;> native_decide

example (form : CorrelationPathFormTag) :
    CorrelationPathFormTag.all.contains form = true := by
  cases form <;> native_decide

example (form : CorrelationStarPathFormTag) :
    CorrelationStarPathFormTag.all.contains form = true := by
  cases form <;> native_decide

example (scope : ReferencedScopeTag) : ReferencedScopeTag.all.contains scope = true := by
  cases scope <;> native_decide

example (form : RawCellFormTag) : RawCellFormTag.all.contains form = true := by
  cases form <;> native_decide

example (form : CorrelationCellFormTag) :
    CorrelationCellFormTag.all.contains form = true := by
  cases form <;> native_decide

example (cause : RejectedCauseTag) : RejectedCauseTag.all.contains cause = true := by
  cases cause <;> native_decide

example (verdict : VerdictTag) : VerdictTag.all.contains verdict = true := by
  cases verdict <;> native_decide

example (category : DiagnosticCategory) : DiagnosticCategory.all.contains category = true := by
  cases category <;> native_decide

example (code : DiagnosticCode) : DiagnosticCode.all.contains code = true := by
  cases code <;> native_decide

example (exclusion : KnownExclusion) : KnownExclusion.all.contains exclusion = true := by
  cases exclusion <;> native_decide

example : ComparisonOperator.supported = [.equal, .notEqual] := by
  native_decide

example : comparisonMatrix.map (·.fieldKind) = FieldKindTag.all := by
  native_decide

example : comparisonMatrix.all fun capability =>
    capability.operators == ComparisonOperator.supported := by
  native_decide

example : (Operation.all.map Operation.tag).Nodup ∧
    (ComparisonOperator.all.map ComparisonOperator.tag).Nodup ∧
    (FieldKindTag.all.map FieldKindTag.tag).Nodup ∧
    (ConditionFormTag.all.map ConditionFormTag.tag).Nodup ∧
    (CorrelatedHavingFormTag.all.map CorrelatedHavingFormTag.tag).Nodup ∧
    (HavingOriginTag.all.map HavingOriginTag.tag).Nodup ∧
    (LiteralKindTag.all.map LiteralKindTag.tag).Nodup ∧
    (PathFormTag.all.map PathFormTag.tag).Nodup ∧
    (CorrelationPathFormTag.all.map CorrelationPathFormTag.tag).Nodup ∧
    (CorrelationStarPathFormTag.all.map CorrelationStarPathFormTag.tag).Nodup ∧
    (ReferencedScopeTag.all.map ReferencedScopeTag.tag).Nodup ∧
    (RawCellFormTag.all.map RawCellFormTag.tag).Nodup ∧
    (CorrelationCellFormTag.all.map CorrelationCellFormTag.tag).Nodup ∧
    (RejectedCauseTag.all.map RejectedCauseTag.tag).Nodup ∧
    (VerdictTag.all.map VerdictTag.tag).Nodup ∧
    (DiagnosticCategory.all.map DiagnosticCategory.tag).Nodup ∧
    (DiagnosticCode.all.map DiagnosticCode.tag).Nodup ∧
    (KnownExclusion.all.map KnownExclusion.tag).Nodup := by
  native_decide

example : ComparisonOperator.all.all fun operator =>
    ComparisonOperator.fromTag? operator.tag == some operator := by
  native_decide

example : ComparisonOperator.all.all fun operator =>
    ComparisonOperator.ofSurface operator.toSurface == operator := by
  native_decide

example : tagsRoundTrip Operation.all Operation.tag Operation.fromTag? &&
    tagsRoundTrip FieldKindTag.all FieldKindTag.tag FieldKindTag.fromTag? &&
    tagsRoundTrip ConditionFormTag.all ConditionFormTag.tag ConditionFormTag.fromTag? &&
    tagsRoundTrip CorrelatedHavingFormTag.all CorrelatedHavingFormTag.tag
      CorrelatedHavingFormTag.fromTag? &&
    tagsRoundTrip HavingOriginTag.all HavingOriginTag.tag HavingOriginTag.fromTag? &&
    tagsRoundTrip LiteralKindTag.all LiteralKindTag.tag LiteralKindTag.fromTag? &&
    tagsRoundTrip PathFormTag.all PathFormTag.tag PathFormTag.fromTag? &&
    tagsRoundTrip CorrelationPathFormTag.all CorrelationPathFormTag.tag
      CorrelationPathFormTag.fromTag? &&
    tagsRoundTrip CorrelationStarPathFormTag.all CorrelationStarPathFormTag.tag
      CorrelationStarPathFormTag.fromTag? &&
    tagsRoundTrip ReferencedScopeTag.all ReferencedScopeTag.tag ReferencedScopeTag.fromTag? &&
    tagsRoundTrip RawCellFormTag.all RawCellFormTag.tag RawCellFormTag.fromTag? &&
    tagsRoundTrip CorrelationCellFormTag.all CorrelationCellFormTag.tag
      CorrelationCellFormTag.fromTag? &&
    tagsRoundTrip RejectedCauseTag.all RejectedCauseTag.tag RejectedCauseTag.fromTag? &&
    tagsRoundTrip VerdictTag.all VerdictTag.tag VerdictTag.fromTag? &&
    tagsRoundTrip DiagnosticCategory.all DiagnosticCategory.tag DiagnosticCategory.fromTag? &&
    tagsRoundTrip KnownExclusion.all KnownExclusion.tag KnownExclusion.fromTag? = true := by
  native_decide

example : ComparisonOperator.fromTag? "greaterEqual" = some .greaterEqual := by
  native_decide

example : FieldKindTag.fromTag? "number" = some .number := by
  native_decide

example : PathFormTag.classify (.relative 0) ["Child"] = none := by
  native_decide

example : PathFormTag.classify (.relative 1) ["Sibling"] = some .parentRelative := by
  native_decide

example : CorrelationPathFormTag.classify (.relative 0) ["Items"] =
    some .childRelative := by
  native_decide

example : CorrelationPathFormTag.classify (.relative 0) ["Sub", "Items"] = none := by
  native_decide

example : CorrelationPathFormTag.classify (.relative 0) [] = none := by
  native_decide

example : CorrelationStarPathFormTag.classify (.relative 0) [] =
    some .directChildRelative := by
  native_decide

example : CorrelationStarPathFormTag.classify (.relative 0) ["Sub"] = none := by
  native_decide

example : CorrelationCellFormTag.classify .parsedNumber none = some .parsedNumber := by
  native_decide

example : CorrelationCellFormTag.classify .rejected (some .malformed) =
    some .rejectedMalformed := by
  native_decide

example : CorrelationCellFormTag.classify .rejected (some .declaredConstraint) = none := by
  native_decide

example : ComparisonOperator.unsupported = [.less, .lessEqual, .greater, .greaterEqual] := by
  native_decide

example : (DiagnosticCode.all.map DiagnosticCode.category).eraseDups =
    DiagnosticCategory.all := by
  native_decide

end A12Kernel.Reference.Support
