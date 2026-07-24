import A12Kernel.Basic
import A12Kernel.Elaboration.Flat.Types
import A12Kernel.Reference.StrictJson

/-! # Protocol support vocabulary and public limits -/

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

end A12Kernel.Reference.Support
