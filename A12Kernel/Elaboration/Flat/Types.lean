import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.TemporalFormat
import A12Kernel.Semantics.CustomFieldType
import A12Kernel.Semantics.CheckedEnumeration
import A12Kernel.Semantics.StringFieldPolicy
import A12Kernel.Semantics.NumericTarget
import A12Kernel.Elaboration.NumericScale

/-! # A12Kernel.Elaboration.Flat — checked lowering into the flat core

This capsule starts from structured, parser-independent surface paths and conditions. It resolves absolute, parent-relative including explicit turning-point labels, and bare field references against an expanded flat model, rejects unsupported or ambiguous input, and lowers accepted conditions into the existing typed non-repeatable core. A quote-aware structured adapter retains whether each field/group name was single-quoted, validates collisions against an injected exact-language keyword profile, erases only the accepted quote syntax, and then delegates to the same resolver. Concrete EN/DE text parsing, stars, semantic indices, and repeatable evaluation remain outside this fragment.
-/

/-! This focused module owns the parser-independent surface syntax, checked model declarations, and diagnostic types. -/

namespace A12Kernel

abbrev GroupPath := List String

namespace FieldId

/-- Return the first authored field identifier whose same identifier occurs again later in the list. -/
def firstDuplicate? : List FieldId → Option FieldId
  | [] => none
  | field :: remaining =>
      if remaining.contains field then some field
      else firstDuplicate? remaining

end FieldId

inductive PathBase where
  | absolute
  | relative (parents : Nat)
  deriving Repr, DecidableEq

/-- A turning-point label belongs only to a positive relative parent walk. -/
def PathBase.allowsTurningPoint : PathBase → Option String → Bool
  | .absolute, turningPoint => turningPoint.isNone
  | .relative parents, turningPoint => parents > 0 || turningPoint.isNone

/-- A field path after concrete syntax has decoded quoting and path separators. For a
    relative path, `parents = 0`, `groups = []` is the bare-name form and therefore uses
    the documented declaring-group → flag-gated model-wide lookup order. There is no
    implicit ancestor walk; parent lookup requires an explicit `parents > 0`. -/
structure SurfaceFieldPath where
  base : PathBase
  /-- Optional authored name of the group reached by a positive parent count. It validates that turning point but never changes how many levels are crossed. -/
  turningPoint : Option String := none
  groups : List String
  field : String
  deriving Repr, DecidableEq

/-- The exact selected condition language's terminal spellings. Membership is deliberately case-sensitive; callers derive this finite profile from the language version they support. -/
structure PathKeywordProfile where
  reserved : List String
  deriving Repr, DecidableEq

/-- One already-tokenized entity name, retaining whether the author used the grammar's single-quote escape. -/
structure AuthoredPathName where
  text : String
  quoted : Bool := false
  deriving Repr, DecidableEq

/-- A structured field path before keyword-quote validation. Path separators and parent counts have already been decoded, but quote provenance remains available to the checked boundary. -/
structure AuthoredFieldPath where
  base : PathBase
  turningPoint : Option AuthoredPathName := none
  groups : List AuthoredPathName
  field : AuthoredPathName
  deriving Repr, DecidableEq

inductive PathSyntaxError where
  | unquotedKeyword (name : String)
  deriving Repr, DecidableEq

/-- A direct textual field operand or one exact Enumeration category access after concrete syntax has decoded `->`. -/
inductive SurfaceTextFieldOperand where
  | direct (field : SurfaceFieldPath)
  | category (field : SurfaceFieldPath) (name : String)
  deriving Repr, DecidableEq

inductive SurfaceComparisonOp where
  | equal
  | notEqual
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving Repr, DecidableEq

/-- Authored operand position of a point-in-time source. `Today` and `Now` comparison syntax permit either side. -/
inductive SurfacePointInTimePosition where
  | left
  | right
  deriving Repr, DecidableEq

inductive SurfaceLiteral where
  | number (value : Rat)
  | boolean (value : Bool)
  | string (value : String)
  | date (components : TemporalComponents) (instant : Instant)
  deriving Repr, DecidableEq

inductive SurfaceScalarKind where
  | number
  | boolean
  | confirm
  | string
  | enumeration
  | temporal (kind : TemporalKind)
  deriving Repr, DecidableEq

/-- Whether a String declaration exposes an evaluation value. Raw Strings retain storage presence but close every checked value-reading route. -/
inductive StringValueMode where
  | evaluated
  | raw
  deriving Repr, DecidableEq

/-- The two model-owned requiredness policies. The first is absolute only without a repeatable ancestor; otherwise it is gated by the nearest repeatable ancestor. -/
inductive RequirednessMode where
  | absoluteOrNearestRepeatableAncestor
  | relativeToParent
  deriving Repr, DecidableEq

namespace SurfaceLiteral

def kind : SurfaceLiteral → SurfaceScalarKind
  | .number _ => .number
  | .boolean _ => .boolean
  | .string _ => .string
  | .date _ _ => .temporal .date

end SurfaceLiteral

inductive SurfaceCondition where
  | compare (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
      (literal : SurfaceLiteral)
  | compareFields (op : SurfaceComparisonOp) (left right : SurfaceFieldPath)
  | compareTextFields (op : SurfaceComparisonOp)
      (left right : SurfaceTextFieldOperand)
  | compareToday (op : SurfaceComparisonOp) (position : SurfacePointInTimePosition)
      (field : SurfaceFieldPath)
  | compareBaseYear (op : SurfaceComparisonOp) (position : SurfacePointInTimePosition)
      (field : SurfaceFieldPath)
  | compareBaseYearRange (op : SurfaceComparisonOp)
      (position : SurfacePointInTimePosition) (endpoint : BaseYearRangeEndpoint)
      (field : SurfaceFieldPath)
  | compareNow (op : SurfaceComparisonOp) (position : SurfacePointInTimePosition)
      (field : SurfaceFieldPath)
  | compareEnumeration (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
      (projection : EnumerationProjectionRef) (literal : String)
  | enumerationValueList (quantifier : ValueListQuantifier)
      (fields : List SurfaceTextFieldOperand) (values : List String)
  | enumerationFieldValueList (quantifier : ValueListQuantifier)
      (fields values : List SurfaceTextFieldOperand)
  | stringValueList (quantifier : ValueListQuantifier)
      (fields : List SurfaceFieldPath) (values : List String)
  | stringFieldValueList (quantifier : ValueListQuantifier)
      (fields values : List SurfaceFieldPath)
  | stringValueMembership (op : ValueListMembershipOp)
      (field : SurfaceFieldPath) (values : List String)
  | stringFieldValueMembership (op : ValueListMembershipOp)
      (field : SurfaceFieldPath) (values : List SurfaceFieldPath)
  | numberValueMembership (op : ValueListMembershipOp)
      (field : SurfaceFieldPath) (values : List Int)
  | numberFieldValueMembership (op : ValueListMembershipOp)
      (field : SurfaceFieldPath) (values : List SurfaceFieldPath)
  | numberFieldValueList (quantifier : ValueListQuantifier)
      (fields values : List SurfaceFieldPath)
  | enumerationValueMembership (op : ValueListMembershipOp)
      (field : SurfaceTextFieldOperand) (values : List String)
  | enumerationFieldValueMembership (op : ValueListMembershipOp)
      (field : SurfaceTextFieldOperand) (values : List SurfaceTextFieldOperand)
  | lengthCompare (op : SurfaceComparisonOp) (field : SurfaceFieldPath) (literal : Rat)
  | literalCompareLength (literal : Rat) (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
  | fieldFilled (field : SurfaceFieldPath)
  | fieldNotFilled (field : SurfaceFieldPath)
  | and (left right : SurfaceCondition)
  | or (left right : SurfaceCondition)
  deriving Repr, DecidableEq

/-- One expanded field declaration. `repeatableScope` lists every repeatable ancestor;
    the current capsule accepts exactly the empty list. -/
structure FlatFieldDecl where
  id : FieldId
  groupPath : GroupPath
  name : String
  policy : FieldPolicy
  stringValueMode : StringValueMode := .evaluated
  stringPolicy : StringFieldPolicy := {}
  /-- Exact declared pattern source retained independently of condition-pattern execution. String-value consumers receive the declaration capability here and rely on their prepared or caller-checked context for pattern execution. -/
  stringPatternSource : Option String := none
  customType : Option CustomFieldTypeDeclaration := none
  enumeration : Option EnumerationDeclaration := none
  /-- Absence means that this field has no model-declared generated mandatory rule. -/
  requiredness : Option RequirednessMode := none
  /-- Resolved Number constraints reachable from computed-target checking. Scale and signedness remain in `policy.kind`. -/
  numericTargetConstraints : NumericTargetConstraints :=
    NumericTargetConstraints.unconstrained
  repeatableScope : List RepeatableLevel := []
  deriving Repr, DecidableEq

namespace FlatFieldDecl

def path (declaration : FlatFieldDecl) : List String :=
  declaration.groupPath ++ [declaration.name]

/-- The exact model-owned capability used by every checked String value consumer. Presence deliberately does not use this projection. -/
def toStringValueField? (declaration : FlatFieldDecl) : Option FlatStringField :=
  match declaration.policy.kind, declaration.stringValueMode with
  | .string, .evaluated => some { id := declaration.id }
  | _, _ => none

def isRawString (declaration : FlatFieldDecl) : Bool :=
  declaration.policy.kind == .string && declaration.stringValueMode == .raw

/-- Convert one expanded declaration to the shared resolved Number-field representation. -/
def toNumberField? (declaration : FlatFieldDecl) : Option FlatNumberField :=
  match declaration.policy.kind with
  | .number info => some { id := declaration.id, info }
  | .boolean | .confirm | .string | .enumeration | .temporal _ _ => none

/-- Construct the complete computed-Number target policy from this declaration without accepting caller-supplied constraints. -/
def toNumericTargetPolicy? (declaration : FlatFieldDecl) :
    Option NumericTargetPolicy :=
  match declaration.policy.kind with
  | .number info => declaration.numericTargetConstraints.toPolicy? info
  | .boolean | .confirm | .string | .enumeration | .temporal _ _ => none

/-- Convert one expanded declaration to the shared resolved temporal-field representation. -/
def toTemporalField? (declaration : FlatFieldDecl) : Option FlatTemporalField :=
  match declaration.policy.kind with
  | .temporal kind components => some { id := declaration.id, kind, components }
  | .number _ | .boolean | .confirm | .string | .enumeration => none

def toPresenceField (declaration : FlatFieldDecl) : FlatField :=
  match declaration.policy.kind with
  | .number info => .number { id := declaration.id, info }
  | .boolean => .boolean { id := declaration.id }
  | .confirm => .confirm { id := declaration.id }
  | .string => .string { id := declaration.id }
  | .enumeration => .enumeration { id := declaration.id }
  | .temporal kind components =>
      .temporal { id := declaration.id, kind, components }

/-- Resolve one exact stored/category projection from a legal Enumeration declaration for direct textual comparison. Category access is statically exempt from display-remapping compatibility. -/
def toEnumerationTextFieldComparison? (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef) :
    Option (FlatTextFieldOperand × DirectComparableField) :=
  match declaration.policy.kind, declaration.enumeration with
  | .enumeration, some source =>
      match elaborateEnumeration source with
      | .ok checked =>
          match checked.resolveProjection projectionRef with
          | .ok projection =>
              let profile := match projectionRef with
                | .stored => checked.directComparableField
                | .category _ => .category
              some (.enumeration {
                field := { id := declaration.id }
                projectionRef
                projection }, profile)
          | .error _ => none
      | .error _ => none
  | _, _ => none

/-- Resolve one legal direct String/Enumeration declaration to its stored-value runtime operand and independent static-comparability profile. -/
def toTextFieldComparison? (declaration : FlatFieldDecl) :
    Option (FlatTextFieldOperand × DirectComparableField) :=
  match declaration.toStringValueField?, declaration.policy.kind,
      declaration.enumeration with
  | some field, .string, none => some (.string field, .plainString)
  | none, .enumeration, some _ => declaration.toEnumerationTextFieldComparison? .stored
  | _, _, _ => none

def textComparisonProfileFor? (declaration : FlatFieldDecl)
    (operand : FlatTextFieldOperand) : Option DirectComparableField :=
  let resolved := match operand with
    | .string _ => declaration.toTextFieldComparison?
    | .enumeration operand =>
        declaration.toEnumerationTextFieldComparison? operand.projectionRef
  resolved.bind fun (checkedOperand, profile) =>
    if checkedOperand == operand then some profile else none

end FlatFieldDecl

/-- One repeatable model level with the exact group path on which `*` may be written. A field's `repeatableScope` alone cannot identify that path segment. -/
structure RepeatableGroupDecl where
  level : RepeatableLevel
  path : GroupPath
  /-- Declared maximum row count when the staged model boundary retains it. -/
  repeatability : Option Nat := none
  /-- The unique direct-child field used for semantic row selection, when declared. -/
  indexField : Option FieldId := none
  deriving Repr, DecidableEq

structure FlatModel where
  fields : List FlatFieldDecl
  repeatableGroups : List RepeatableGroupDecl := []
  fieldRefByShortNameAllowed : Bool := false
  baseYear : Option Int := none
  /-- Exact legacy zone id already admitted by the upstream model checker. Absent model configuration is normalized to UTC. -/
  timeZoneId : String := "UTC"
  deriving Repr, DecidableEq

def FlatModel.hasBaseYear (model : FlatModel) : Bool := model.baseYear.isSome

/-- The resolved gate of a model-declared required field. -/
inductive RequirednessScope where
  | absolute
  | relativeTo (groupPath : GroupPath)
  deriving Repr, DecidableEq

inductive ResolveError where
  | invalidModelPath (path : List String)
  | duplicateFieldId (id : FieldId)
  | duplicateEntityPath (path : List String)
  | customTypeRequiresString (path : List String)
  | rawValueModeRequiresString (path : List String)
  | rawValueModeForbidsCustomType (path : List String)
  | stringPolicyRequiresString (path : List String)
  | stringPolicyForbidsCustomType (path : List String)
  | stringPatternRequiresString (path : List String)
  | stringPatternForbidsCustomType (path : List String)
  | numericTargetConstraintsRequireNumber (path : List String)
  | numericMinimumFractionalDigitsExceedMaximum (path : List String)
      (minimum maximum : Nat)
  | numericMaximumIntegerDigitsZero (path : List String)
  | rawStringRequiresLineBreakPermission (path : List String)
  | rawStringForbidsMinimumLength (path : List String)
  | rawStringForbidsPattern (path : List String)
  | stringMinimumExceedsMaximum (path : List String)
  | lineBreakWithSingleCharacterMaximum (path : List String)
  | enumerationMetadataRequiresEnumeration (path : List String)
  | enumerationDeclarationRequired (path : List String)
  | invalidEnumerationDeclaration (path : List String)
      (error : EnumerationDeclarationError)
  | invalidRepeatableGroupPath (path : GroupPath)
  | duplicateRepeatableGroupPath (path : GroupPath)
  | duplicateRepeatableLevel (level : RepeatableLevel)
  | invalidIndexField (groupPath : GroupPath) (field : FieldId)
  | entityHierarchyCollision (fieldPath groupPath : GroupPath)
  | repeatableScopeMismatch (path : List String)
      (expected actual : List RepeatableLevel)
  | unknownRepeatableGroup (path : GroupPath)
  | unknownFieldId (id : FieldId)
  | invalidRuleGroup (path : GroupPath)
  | invalidReference (reference : SurfaceFieldPath)
  | aboveRoot (parents : Nat)
  | invalidEntity (reference : SurfaceFieldPath)
  | ambiguousEntity (path : List String)
  | shortNameNotUnique (name : String)
  | repeatableReference (path : List String)
  deriving Repr, DecidableEq

inductive AuthoredFieldPathError where
  | syntax (error : PathSyntaxError)
  | resolve (error : ResolveError)
  deriving Repr, DecidableEq

inductive ElabError where
  | resolve (error : ResolveError)
  | unsupportedOperator (op : SurfaceComparisonOp)
  | literalKindMismatch (path : List String) (expected actual : SurfaceScalarKind)
  | illegalConfirmLiteral (path : List String)
  | temporalOperandKindMismatch (leftPath rightPath : List String)
      (leftKind rightKind : SurfaceScalarKind)
  | temporalFormatsIncompatible (leftPath rightPath : List String)
  | temporalNowRequiresTime (path : List String)
  | baseYearNotDeclared
  | baseYearScaleMismatch (path : List String) (fieldScale : Nat)
  | temporalLiteralNeedsBaseYear (path : List String)
  | invalidTemporalLiteralComponents (path : List String)
  | rawStringValue (path : List String)
  | rawStringLength (path : List String)
  | lengthOperandKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | enumerationOperand (path : List String) (error : EnumerationOperandError)
  | textFieldOperandKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | emptyValueList (path : List String)
  | emptyValueListFields
  | emptyValueListValueFields
  | duplicateValueListField (path : List String)
      (projectionRef : EnumerationProjectionRef)
  | duplicateStringValueListField (path : List String)
  | duplicateNumberValueListField (path : List String)
  | enumerationComparability (leftPath rightPath : List String)
      (error : EnumerationComparabilityError)
  | incoherentCore
  deriving Repr, DecidableEq

end A12Kernel
