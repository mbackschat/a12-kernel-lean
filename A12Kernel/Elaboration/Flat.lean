import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.TemporalFormat
import A12Kernel.Semantics.CustomFieldType
import A12Kernel.Semantics.CheckedEnumeration
import A12Kernel.Elaboration.NumericScale

/-! # A12Kernel.Elaboration.Flat — checked lowering into the flat core

This capsule starts from structured, parser-independent surface paths and conditions. It
resolves absolute, parent-relative, and bare field references against an expanded flat
model, rejects unsupported or ambiguous input, and lowers accepted conditions into the
existing typed non-repeatable core. Quoting, named-ancestor labels, stars, semantic
indices, concrete EN/DE syntax, and repeatable evaluation remain outside this fragment.
-/

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

/-- A field path after concrete syntax has decoded quoting and path separators. For a
    relative path, `parents = 0`, `groups = []` is the bare-name form and therefore uses
    the documented declaring-group → flag-gated model-wide lookup order. There is no
    implicit ancestor walk; parent lookup requires an explicit `parents > 0`. -/
structure SurfaceFieldPath where
  base : PathBase
  groups : List String
  field : String
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
  customType : Option CustomFieldTypeDeclaration := none
  enumeration : Option EnumerationDeclaration := none
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

inductive ResolveError where
  | invalidModelPath (path : List String)
  | duplicateFieldId (id : FieldId)
  | duplicateEntityPath (path : List String)
  | customTypeRequiresString (path : List String)
  | rawValueModeRequiresString (path : List String)
  | rawValueModeForbidsCustomType (path : List String)
  | enumerationMetadataRequiresEnumeration (path : List String)
  | enumerationDeclarationRequired (path : List String)
  | invalidEnumerationDeclaration (path : List String)
      (error : EnumerationDeclarationError)
  | invalidRepeatableGroupPath (path : GroupPath)
  | duplicateRepeatableGroupPath (path : GroupPath)
  | duplicateRepeatableLevel (level : RepeatableLevel)
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

private def validName (name : String) : Bool := !name.isEmpty

def GroupPath.isValid (path : GroupPath) : Bool :=
  !path.isEmpty && path.all validName

def GroupPath.isPrefixOf : GroupPath → GroupPath → Bool
  | [], _ => true
  | _, [] => false
  | prefixHead :: prefixRest, segment :: pathRest =>
      prefixHead == segment && GroupPath.isPrefixOf prefixRest pathRest

private def FlatFieldDecl.hasValidPath (declaration : FlatFieldDecl) : Bool :=
  GroupPath.isValid declaration.groupPath && validName declaration.name

private def invalidDeclPath? : List FlatFieldDecl → Option (List String)
  | [] => none
  | declaration :: rest =>
      if declaration.hasValidPath then invalidDeclPath? rest else some declaration.path

private def duplicateId? : List FlatFieldDecl → Option FieldId
  | [] => none
  | declaration :: rest =>
      if rest.any (fun candidate => candidate.id == declaration.id) then
        some declaration.id
      else
        duplicateId? rest

private def duplicatePath? : List FlatFieldDecl → Option (List String)
  | [] => none
  | declaration :: rest =>
      if rest.any (fun candidate => candidate.path == declaration.path) then
        some declaration.path
      else
        duplicatePath? rest

private def customTypeKindMismatch? : List FlatFieldDecl → Option (List String)
  | [] => none
  | declaration :: rest =>
      match declaration.customType, declaration.policy.kind with
      | none, _ => customTypeKindMismatch? rest
      | some _, .string => customTypeKindMismatch? rest
      | some _, _ => some declaration.path

private def rawValueModeError? : List FlatFieldDecl → Option ResolveError
  | [] => none
  | declaration :: rest =>
      match declaration.stringValueMode, declaration.policy.kind,
          declaration.customType with
      | .evaluated, _, _ => rawValueModeError? rest
      | .raw, .string, none => rawValueModeError? rest
      | .raw, .string, some _ =>
          some (.rawValueModeForbidsCustomType declaration.path)
      | .raw, _, _ => some (.rawValueModeRequiresString declaration.path)

private def enumerationDeclarationError? :
    List FlatFieldDecl → Option ResolveError
  | [] => none
  | declaration :: rest =>
      match declaration.policy.kind, declaration.enumeration with
      | .enumeration, none => some (.enumerationDeclarationRequired declaration.path)
      | .enumeration, some source =>
          match source.validate with
          | .error error => some (.invalidEnumerationDeclaration declaration.path error)
          | .ok () => enumerationDeclarationError? rest
      | _, some _ => some (.enumerationMetadataRequiresEnumeration declaration.path)
      | _, none => enumerationDeclarationError? rest

private def invalidRepeatableGroupPath? : List RepeatableGroupDecl → Option GroupPath
  | [] => none
  | group :: rest =>
      if GroupPath.isValid group.path then invalidRepeatableGroupPath? rest else some group.path

private def duplicateRepeatableGroupPath? : List RepeatableGroupDecl → Option GroupPath
  | [] => none
  | group :: rest =>
      if rest.any (fun candidate => candidate.path == group.path) then
        some group.path
      else
        duplicateRepeatableGroupPath? rest

private def duplicateRepeatableLevel? : List RepeatableGroupDecl → Option RepeatableLevel
  | [] => none
  | group :: rest =>
      if rest.any (fun candidate => candidate.level == group.level) then
        some group.level
      else
        duplicateRepeatableLevel? rest

private def prefixedGroupPath? (fieldPath : GroupPath) :
    List GroupPath → Option GroupPath
  | [] => none
  | groupPath :: rest =>
      if fieldPath.isPrefixOf groupPath then some groupPath
      else prefixedGroupPath? fieldPath rest

private def entityHierarchyCollision? (groupPaths : List GroupPath) :
    List FlatFieldDecl → Option (GroupPath × GroupPath)
  | [] => none
  | declaration :: rest =>
      match prefixedGroupPath? declaration.path groupPaths with
      | some groupPath => some (declaration.path, groupPath)
      | none => entityHierarchyCollision? groupPaths rest

/-- Derive the canonical outer-to-inner repeatable ancestry from declared group paths. -/
def FlatModel.repeatableScopeForGroupPath (model : FlatModel) (groupPath : GroupPath) :
    List RepeatableLevel :=
  (List.range groupPath.length).filterMap fun offset =>
    (model.repeatableGroups.find? fun group =>
      group.path == groupPath.take (offset + 1)).map (·.level)

private def repeatableScopeMismatch? (model : FlatModel) :
    List FlatFieldDecl →
      Option (List String × List RepeatableLevel × List RepeatableLevel)
  | [] => none
  | declaration :: rest =>
      let expected := model.repeatableScopeForGroupPath declaration.groupPath
      if declaration.repeatableScope == expected then
        repeatableScopeMismatch? model rest
      else
        some (declaration.path, expected, declaration.repeatableScope)

def FlatModel.validate (model : FlatModel) : Except ResolveError Unit := do
  match invalidDeclPath? model.fields with
  | some path => throw (.invalidModelPath path)
  | none => pure ()
  match customTypeKindMismatch? model.fields with
  | some path => throw (.customTypeRequiresString path)
  | none => pure ()
  match rawValueModeError? model.fields with
  | some error => throw error
  | none => pure ()
  match enumerationDeclarationError? model.fields with
  | some error => throw error
  | none => pure ()
  match duplicateId? model.fields with
  | some id => throw (.duplicateFieldId id)
  | none => pure ()
  match duplicatePath? model.fields with
  | some path => throw (.duplicateEntityPath path)
  | none => pure ()
  match invalidRepeatableGroupPath? model.repeatableGroups with
  | some path => throw (.invalidRepeatableGroupPath path)
  | none => pure ()
  match duplicateRepeatableGroupPath? model.repeatableGroups with
  | some path => throw (.duplicateRepeatableGroupPath path)
  | none => pure ()
  match duplicateRepeatableLevel? model.repeatableGroups with
  | some level => throw (.duplicateRepeatableLevel level)
  | none => pure ()
  let groupPaths := model.fields.map (·.groupPath) ++ model.repeatableGroups.map (·.path)
  match entityHierarchyCollision? groupPaths model.fields with
  | some (fieldPath, groupPath) =>
      throw (.entityHierarchyCollision fieldPath groupPath)
  | none => pure ()
  match repeatableScopeMismatch? model model.fields with
  | some (path, expected, actual) =>
      throw (.repeatableScopeMismatch path expected actual)
  | none => pure ()

/-- Unique lookup is intentionally order-independent: ambiguity is an error, never a
    first-match choice. -/
def FlatModel.lookupUniqueId (model : FlatModel) (id : FieldId) :
    Except ResolveError FlatFieldDecl :=
  match model.fields.filter (fun declaration => declaration.id == id) with
  | [] => .error (.unknownFieldId id)
  | [declaration] => .ok declaration
  | _ => .error (.duplicateFieldId id)

/-- Look up the declaration proving that an exact written group path is repeatable. -/
def FlatModel.lookupUniqueRepeatablePath (model : FlatModel) (path : GroupPath) :
    Except ResolveError RepeatableGroupDecl :=
  match model.repeatableGroups.filter (fun group => group.path == path) with
  | [] => .error (.unknownRepeatableGroup path)
  | [group] => .ok group
  | _ => .error (.duplicateRepeatableGroupPath path)

private def FlatModel.lookupPath? (model : FlatModel) (path : List String) :
    Except ResolveError (Option FlatFieldDecl) :=
  match model.fields.filter (fun declaration => declaration.path == path) with
  | [] => .ok none
  | [declaration] => .ok (some declaration)
  | _ => .error (.ambiguousEntity path)

private def SurfaceFieldPath.hasValidShape (reference : SurfaceFieldPath) : Bool :=
  validName reference.field && reference.groups.all validName &&
    match reference.base with
    | .absolute => !reference.groups.isEmpty
    | .relative _ => true

def GroupPath.walkUp (group : GroupPath) (parents : Nat) : Except ResolveError GroupPath :=
  if parents < group.length then
    .ok (group.take (group.length - parents))
  else
    .error (.aboveRoot parents)

def FlatFieldDecl.requireNonrepeatable (declaration : FlatFieldDecl) :
    Except ResolveError FlatFieldDecl :=
  if declaration.repeatableScope.isEmpty then
    .ok declaration
  else
    .error (.repeatableReference declaration.path)

/-- Resolve one declaration by stable ID and reject repeatable targets or operands. -/
def FlatModel.resolveNonrepeatableDeclarationById
    (model : FlatModel) (field : FieldId) :
    Except ResolveError FlatFieldDecl := do
  (← model.lookupUniqueId field).requireNonrepeatable

/-- Resolve a bare single-segment reference exactly as the kernel parser does: try the
    declaring group, then (when enabled) require one model-wide short-name match. There
    is deliberately no implicit ancestor walk; parent lookup requires `..`. -/
private def FlatModel.resolveBareDeclaration (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl := do
  match ← model.lookupPath? (declaringGroup ++ [reference.field]) with
  | some declaration => pure declaration
  | none =>
      if model.fieldRefByShortNameAllowed then
        match model.fields.filter (fun declaration => declaration.name == reference.field) with
        | [] => throw (.invalidEntity reference)
        | [declaration] => pure declaration
        | _ => throw (.shortNameNotUnique reference.field)
      else
        throw (.invalidEntity reference)

/-- Shared path mechanism for both non-repeatable and repeatable elaborators. This resolves one declaration without deciding whether its repeatable scope is legal for the caller. -/
def FlatModel.resolveFieldDeclarationUnchecked (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FlatFieldDecl := do
  if !GroupPath.isValid declaringGroup then throw (.invalidRuleGroup declaringGroup)
  if !reference.hasValidShape then throw (.invalidReference reference)
  match reference.base with
  | .absolute =>
      match ← model.lookupPath? (reference.groups ++ [reference.field]) with
      | some declaration => pure declaration
      | none => throw (.invalidEntity reference)
  | .relative parents =>
      if parents == 0 && reference.groups.isEmpty then
        model.resolveBareDeclaration declaringGroup reference
      else
        let base ← GroupPath.walkUp declaringGroup parents
        match ← model.lookupPath? (base ++ reference.groups ++ [reference.field]) with
        | some declaration => pure declaration
        | none => throw (.invalidEntity reference)

/-- Resolve a nonrepeatable declaration after a caller has validated the model. This is shared by checked condition and computation-expression lowering. -/
def FlatModel.resolveNonrepeatableFieldUnchecked (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FlatFieldDecl := do
  (← model.resolveFieldDeclarationUnchecked declaringGroup reference).requireNonrepeatable

/-- Resolve one structured field path against a validated expanded model while preserving its repeatable scope for a later elaborator. -/
def FlatModel.resolveFieldDeclaration (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl := do
  model.validate
  model.resolveFieldDeclarationUnchecked declaringGroup reference

/-- Resolve one structured field path against a validated expanded model. -/
def FlatModel.resolveField (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl := do
  model.validate
  model.resolveNonrepeatableFieldUnchecked declaringGroup reference

def FieldKind.surfaceKind : FieldKind → SurfaceScalarKind
  | .number _ => .number
  | .boolean => .boolean
  | .confirm => .confirm
  | .string => .string
  | .enumeration => .enumeration
  | .temporal kind _ => .temporal kind

private def SurfaceComparisonOp.toEquality? : SurfaceComparisonOp → Option EqualityOp
  | .equal => some .equal
  | .notEqual => some .notEqual
  | _ => none

private def SurfaceComparisonOp.toNumeric? : SurfaceComparisonOp → Option NumericComparisonOp
  | .equal => some .equal
  | .notEqual => some .notEqual
  | .less => some .less
  | .lessEqual => some .lessEqual
  | .greater => some .greater
  | .greaterEqual => some .greaterEqual

private def SurfaceComparisonOp.toStringLength? : SurfaceComparisonOp →
    Option StringLengthComparisonOp
  | .less => some .less
  | .lessEqual => some .lessEqual
  | .greater => some .greater
  | .greaterEqual => some .greaterEqual
  | _ => none

private def SurfaceComparisonOp.toTemporal : SurfaceComparisonOp → TemporalComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .less => .before
  | .lessEqual => .beforeOrEqual
  | .greater => .after
  | .greaterEqual => .afterOrEqual

private def SurfaceComparisonOp.swapped : SurfaceComparisonOp → SurfaceComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .less => .greater
  | .lessEqual => .greaterEqual
  | .greater => .less
  | .greaterEqual => .lessEqual

private def temporalPointComparison (comparison : TemporalComparisonOp)
    (position : SurfacePointInTimePosition) (point field : FlatTemporalOperand) :
    FlatCondition :=
  match position with
  | .left => .compare (.temporal comparison point field)
  | .right => .compare (.temporal comparison field point)

private def BaseYearRangeEndpoint.surfacePath : BaseYearRangeEndpoint → List String
  | .start => ["<StartOfDateRange(BaseYear)>"]
  | .finish => ["<EndOfDateRange(BaseYear)>"]

def FlatField.matchesDecl (field : FlatField) (declaration : FlatFieldDecl) : Bool :=
  declaration.toPresenceField == field

def FlatModel.admitsField (model : FlatModel) (field : FlatField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration => declaration.repeatableScope.isEmpty && field.matchesDecl declaration
  | .error _ => false

/-- Stronger than presence admission: the exact nonrepeatable declaration must expose an evaluated String value. -/
def FlatModel.admitsStringValueField (model : FlatModel)
    (field : FlatStringField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toStringValueField? == some field
  | .error _ => false

/-- Re-derive one direct textual operand's static profile from the exact model declaration retained by checked core admission. -/
def FlatModel.directComparableFor? (model : FlatModel)
    (operand : FlatTextFieldOperand) : Option DirectComparableField :=
  match model.lookupUniqueId operand.field.id with
  | .error _ => none
  | .ok declaration =>
      if declaration.repeatableScope.isEmpty &&
          operand.field.matchesDecl declaration then
        declaration.textComparisonProfileFor? operand
      else
        none

/-- Reconstruct the proof-bearing Enumeration projection retained by a flat operand from the exact model declaration. -/
def FlatModel.checkedEnumerationOperand? (model : FlatModel)
    (operand : FlatEnumerationOperand) : Option CheckedEnumerationProjection :=
  match model.lookupUniqueId operand.field.id with
  | .error _ => none
  | .ok declaration =>
      if declaration.repeatableScope.isEmpty &&
          (FlatField.enumeration operand.field).matchesDecl declaration then
        match declaration.policy.kind, declaration.enumeration with
        | .enumeration, some source =>
            match elaborateEnumeration source with
            | .error _ => none
            | .ok checked =>
                match checkEnumerationProjection checked operand.projectionRef with
                | .error _ => none
                | .ok resolved => if resolved.projection == operand.projection then some resolved else none
        | _, _ => none
      else
        none

def FlatModel.enumerationLiteralAllowedByAny (model : FlatModel)
    (operands : List FlatTextFieldOperand) (value : String) : Bool :=
  operands.any fun operand =>
    match operand with
    | .enumeration enumeration =>
      match model.checkedEnumerationOperand? enumeration with
      | some checked =>
        checked.declaration.literalAllowed checked.projection value
      | none => false
    | .string _ => false

inductive FlatTokenOperandKind where
  | string
  | enumeration
  deriving Repr, DecidableEq

def FlatModel.tokenOperandKind? (model : FlatModel) :
    FlatTextFieldOperand → Option FlatTokenOperandKind
  | operand@(.string _) =>
      match model.directComparableFor? operand with
      | some .plainString => some .string
      | _ => none
  | .enumeration operand =>
      if (model.checkedEnumerationOperand? operand).isSome then
        some .enumeration
      else
        none

def tokenOperandListHasDuplicate : List FlatTextFieldOperand → Bool
  | [] => false
  | operand :: remaining =>
      remaining.contains operand || tokenOperandListHasDuplicate remaining

def FlatModel.tokenOperandListKind? (model : FlatModel)
    (operands : List FlatTextFieldOperand) : Option FlatTokenOperandKind :=
  match operands with
  | [] => none
  | first :: remaining => do
      let kind ← model.tokenOperandKind? first
      if !tokenOperandListHasDuplicate operands &&
          remaining.all (fun operand => model.tokenOperandKind? operand == some kind) then
        some kind
      else
        none

def numberOperandListHasDuplicate : List FlatNumberField → Bool
  | [] => false
  | operand :: remaining =>
      remaining.contains operand || numberOperandListHasDuplicate remaining

def FlatModel.admitsNumberOperandList (model : FlatModel)
    (operands : List FlatNumberField) : Bool :=
  !operands.isEmpty && !numberOperandListHasDuplicate operands &&
    operands.all fun operand => model.admitsField (.number operand)

def FlatModel.admitsComparison (model : FlatModel) (comparison : FlatComparison) : Bool :=
  match comparison with
  | .string _ field _ | .stringLength _ field _ =>
      model.admitsStringValueField field
  | .textFields _ left right =>
      match model.directComparableFor? left, model.directComparableFor? right with
      | some leftProfile, some rightProfile =>
          directFieldComparisonAllowed leftProfile rightProfile
      | _, _ => false
  | .enumeration _ operand expected =>
      match model.checkedEnumerationOperand? operand with
      | some checked =>
          checked.declaration.literalAllowed checked.projection expected
      | none => false
  | _ => !comparison.fields.isEmpty && comparison.fields.all model.admitsField

def FlatConditionLeaf.wellFormedBool (condition : FlatConditionLeaf) (model : FlatModel) : Bool :=
  match condition with
  | .compare comparison => model.admitsComparison comparison
  | .tokenValueList _ operands (.literals values) =>
      !values.isEmpty && match model.tokenOperandListKind? operands with
        | some .string => true
        | some .enumeration =>
            values.all (model.enumerationLiteralAllowedByAny operands)
        | none => false
  | .tokenValueList _ operands (.fields valueOperands) =>
      match model.tokenOperandListKind? operands,
          model.tokenOperandListKind? valueOperands with
      | some fieldKind, some valueKind =>
          fieldKind == valueKind &&
            !tokenOperandListHasDuplicate (operands ++ valueOperands)
      | _, _ => false
  | .numberValueList _ operands (.literals values) =>
      operands.length == 1 && model.admitsNumberOperandList operands && !values.isEmpty &&
        values.all fun value => value.den == 1
  | .numberValueList _ operands (.fields valueOperands) =>
      model.admitsNumberOperandList operands &&
        model.admitsNumberOperandList valueOperands &&
        !numberOperandListHasDuplicate (operands ++ valueOperands)
  | .fieldFilled field => model.admitsField field
  | .fieldNotFilled field => model.admitsField field

def FlatCondition.wellFormedBool (condition : FlatCondition) (model : FlatModel) : Bool :=
  condition.allLeaves fun leaf => leaf.wellFormedBool model

def FlatCondition.WellFormed (condition : FlatCondition) (model : FlatModel) : Prop :=
  condition.wellFormedBool model = true

/-- The only source-to-core result accepted by later stages. -/
structure CheckedFlatCondition (model : FlatModel) where
  rowGroup : GroupPath
  core : FlatCondition
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model

/-- Certify a constructed core condition against an already-validated model. This is the shared boundary for ordinary surface lowering and semantic desugarings. -/
def FlatCondition.checkAgainstValidatedModel (condition : FlatCondition)
    (model : FlatModel) (rowGroup : GroupPath)
    (modelValid : model.validate = .ok ()) :
    Except ElabError (CheckedFlatCondition model) :=
  if hCore : condition.wellFormedBool model = true then
    .ok {
      rowGroup
      core := condition
      modelWellFormed := by
        rw [modelValid]
        rfl
      wellFormed := hCore
    }
  else
    .error .incoherentCore

private def elaborateEnumerationCore (declaration : FlatFieldDecl)
    (op : SurfaceComparisonOp) (projectionRef : EnumerationProjectionRef)
    (expected : String) : Except ElabError FlatCondition := do
  let equality ← match op.toEquality? with
    | some equality => pure equality
    | none => throw (.unsupportedOperator op)
  match declaration.policy.kind, declaration.enumeration with
  | .enumeration, some source =>
      match elaborateEnumeration source with
      | .error _ => throw .incoherentCore
      | .ok checked =>
          match classifyEnumerationLiteral checked projectionRef equality expected with
          | .rejected error => throw (.enumerationOperand declaration.path error)
          | .accepted projection =>
              pure (.compare (.enumeration equality {
                field := { id := declaration.id }
                projectionRef
                projection } expected))
  | kind, _ =>
      throw (.literalKindMismatch declaration.path .enumeration kind.surfaceKind)

private def finishTextFieldComparison (op : SurfaceComparisonOp)
    (leftPath rightPath : List String)
    (left right : FlatTextFieldOperand × DirectComparableField) :
    Except ElabError FlatCondition := do
  let equality ← match op.toEquality? with
    | some equality => pure equality
    | none => throw (.unsupportedOperator op)
  match classifyDirectFieldComparison left.2 right.2 with
  | .accepted => pure (.compare (.textFields equality left.1 right.1))
  | .rejected error => throw (.enumerationComparability leftPath rightPath error)

/-- Resolve one direct nonrepeatable stored/category Enumeration operand with its exact checked projection and runtime core. -/
def elaborateEnumerationFieldOperand (model : FlatModel)
    (declaringGroup : GroupPath) (surface : SurfaceTextFieldOperand) :
    Except ElabError
      (List String × CheckedEnumerationProjection × FlatEnumerationOperand) := do
  let reference := match surface with
    | .direct field | .category field _ => field
  let projectionRef : EnumerationProjectionRef := match surface with
    | .direct _ => .stored
    | .category _ name => .category name
  let declaration ←
    (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
  match declaration.policy.kind, declaration.enumeration with
  | .enumeration, some source =>
      match elaborateEnumeration source with
      | .error _ => throw .incoherentCore
      | .ok checked =>
          match checkEnumerationProjection checked projectionRef with
          | .error error => throw (.enumerationOperand declaration.path error)
          | .ok projection =>
              pure (declaration.path, projection, {
                field := { id := declaration.id }
                projectionRef := projection.projectionRef
                projection := projection.projection })
  | kind, _ =>
      throw (.textFieldOperandKindMismatch declaration.path kind.surfaceKind)

private def elaborateEnumerationLiteralList (model : FlatModel)
    (declaringGroup : GroupPath) (surface : SurfaceTextFieldOperand)
    (values : List String) : Except ElabError FlatEnumerationOperand := do
  let (path, checked, operand) ←
    elaborateEnumerationFieldOperand model declaringGroup surface
  if values.isEmpty then
    throw (.emptyValueList path)
  else
    match values.find? fun value =>
        !checked.declaration.literalAllowed checked.projection value with
    | some value => throw (.enumerationOperand path (.invalidLiteral value))
    | none => pure operand

private abbrev ElaboratedEnumerationOperand :=
  List String × CheckedEnumerationProjection × FlatEnumerationOperand

private def duplicateElaboratedEnumerationOperand? :
    List ElaboratedEnumerationOperand →
      Option (List String × EnumerationProjectionRef)
  | [] => none
  | current :: remaining =>
      if remaining.any fun candidate => candidate.2.2 == current.2.2 then
        some (current.1, current.2.2.projectionRef)
      else
        duplicateElaboratedEnumerationOperand? remaining

private def elaborateEnumerationOperandList (model : FlatModel)
    (declaringGroup : GroupPath) (surfaces : List SurfaceTextFieldOperand)
    (emptyError : ElabError) : Except ElabError (List ElaboratedEnumerationOperand) := do
  if surfaces.isEmpty then
    throw emptyError
  surfaces.mapM (elaborateEnumerationFieldOperand model declaringGroup)

private def rejectDuplicateEnumerationOperands
    (resolved : List ElaboratedEnumerationOperand) : Except ElabError Unit :=
  match duplicateElaboratedEnumerationOperand? resolved with
  | some (path, projectionRef) =>
      throw (.duplicateValueListField path projectionRef)
  | none => pure ()

private def elaborateEnumerationLiteralFieldList (model : FlatModel)
    (declaringGroup : GroupPath) (surfaces : List SurfaceTextFieldOperand)
    (values : List String) : Except ElabError (List FlatEnumerationOperand) := do
  let resolved ← elaborateEnumerationOperandList model declaringGroup surfaces
    .emptyValueListFields
  rejectDuplicateEnumerationOperands resolved
  match resolved with
  | [] => throw .emptyValueListFields
  | first :: remaining =>
      if values.isEmpty then
        throw (.emptyValueList first.1)
      else
        match values.find? fun value =>
            !resolved.any fun entry =>
              entry.2.1.declaration.literalAllowed
                entry.2.1.projection value with
        | some value =>
            throw (.enumerationOperand first.1 (.invalidLiteral value))
        | none => pure ((first :: remaining).map (·.2.2))

private def elaborateEnumerationFieldValueSides (model : FlatModel)
    (declaringGroup : GroupPath) (fieldSurfaces valueSurfaces : List SurfaceTextFieldOperand) :
    Except ElabError (List FlatEnumerationOperand × List FlatEnumerationOperand) := do
  let fields ← elaborateEnumerationOperandList model declaringGroup fieldSurfaces
    .emptyValueListFields
  let values ← elaborateEnumerationOperandList model declaringGroup valueSurfaces
    .emptyValueListValueFields
  rejectDuplicateEnumerationOperands (fields ++ values)
  pure (fields.map (·.2.2), values.map (·.2.2))

private abbrev ElaboratedStringValueListOperand := List String × FlatTextFieldOperand

private def requireStringValueField (declaration : FlatFieldDecl) :
    Except ElabError FlatStringField :=
  match declaration.toStringValueField? with
  | some field => pure field
  | none =>
      if declaration.isRawString then
        throw (.rawStringValue declaration.path)
      else
        throw (.textFieldOperandKindMismatch declaration.path
          declaration.policy.kind.surfaceKind)

private def duplicateExactValueListOperand? {operand : Type} [BEq operand] :
    List (List String × operand) → Option (List String)
  | [] => none
  | current :: remaining =>
      if remaining.any fun candidate => candidate.2 == current.2 then
        some current.1
      else
        duplicateExactValueListOperand? remaining

private def elaborateStringValueListOperand (model : FlatModel)
    (declaringGroup : GroupPath) (surface : SurfaceFieldPath) :
    Except ElabError ElaboratedStringValueListOperand := do
  let declaration ←
    (model.resolveNonrepeatableFieldUnchecked declaringGroup surface).mapError .resolve
  let field ← requireStringValueField declaration
  pure (declaration.path, .string field)

private def elaborateStringLiteralList (model : FlatModel)
    (declaringGroup : GroupPath) (surface : SurfaceFieldPath)
    (values : List String) : Except ElabError FlatTextFieldOperand := do
  let (path, operand) ←
    elaborateStringValueListOperand model declaringGroup surface
  if values.isEmpty then
    throw (.emptyValueList path)
  else
    pure operand

private def elaborateStringValueListOperands (model : FlatModel)
    (declaringGroup : GroupPath) (surfaces : List SurfaceFieldPath)
    (emptyError : ElabError) : Except ElabError (List ElaboratedStringValueListOperand) := do
  if surfaces.isEmpty then
    throw emptyError
  surfaces.mapM (elaborateStringValueListOperand model declaringGroup)

private def rejectDuplicateStringValueListOperands
    (resolved : List ElaboratedStringValueListOperand) : Except ElabError Unit :=
  match duplicateExactValueListOperand? resolved with
  | some path => throw (.duplicateStringValueListField path)
  | none => pure ()

private def elaborateStringLiteralFieldList (model : FlatModel)
    (declaringGroup : GroupPath) (surfaces : List SurfaceFieldPath)
    (values : List String) : Except ElabError (List FlatTextFieldOperand) := do
  let resolved ← elaborateStringValueListOperands model declaringGroup surfaces
    .emptyValueListFields
  rejectDuplicateStringValueListOperands resolved
  match resolved with
  | [] => throw .emptyValueListFields
  | first :: remaining =>
      if values.isEmpty then
        throw (.emptyValueList first.1)
      else
        pure ((first :: remaining).map (·.2))

private def elaborateStringFieldValueSides (model : FlatModel)
    (declaringGroup : GroupPath) (fieldSurfaces valueSurfaces : List SurfaceFieldPath) :
    Except ElabError (List FlatTextFieldOperand × List FlatTextFieldOperand) := do
  let fields ← elaborateStringValueListOperands model declaringGroup fieldSurfaces
    .emptyValueListFields
  let values ← elaborateStringValueListOperands model declaringGroup valueSurfaces
    .emptyValueListValueFields
  rejectDuplicateStringValueListOperands (fields ++ values)
  pure (fields.map (·.2), values.map (·.2))

private abbrev ElaboratedNumberValueListOperand := List String × FlatNumberField

private def elaborateNumberValueListOperand (model : FlatModel)
    (declaringGroup : GroupPath) (surface : SurfaceFieldPath) :
    Except ElabError ElaboratedNumberValueListOperand := do
  let declaration ←
    (model.resolveNonrepeatableFieldUnchecked declaringGroup surface).mapError .resolve
  match declaration.toNumberField? with
  | some operand => pure (declaration.path, operand)
  | none =>
      throw (.literalKindMismatch declaration.path .number
        declaration.policy.kind.surfaceKind)

private def elaborateNumberValueListOperands (model : FlatModel)
    (declaringGroup : GroupPath) (surfaces : List SurfaceFieldPath)
    (emptyError : ElabError) : Except ElabError (List ElaboratedNumberValueListOperand) := do
  if surfaces.isEmpty then
    throw emptyError
  surfaces.mapM (elaborateNumberValueListOperand model declaringGroup)

private def rejectDuplicateNumberValueListOperands
    (resolved : List ElaboratedNumberValueListOperand) : Except ElabError Unit :=
  match duplicateExactValueListOperand? resolved with
  | some path => throw (.duplicateNumberValueListField path)
  | none => pure ()

private def elaborateNumberLiteralMembership (model : FlatModel)
    (declaringGroup : GroupPath) (surface : SurfaceFieldPath)
    (values : List Int) : Except ElabError (FlatNumberField × List Rat) := do
  let (path, operand) ←
    elaborateNumberValueListOperand model declaringGroup surface
  if values.isEmpty then
    throw (.emptyValueList path)
  pure (operand, values.map Rat.ofInt)

private def elaborateNumberFieldValueSides (model : FlatModel)
    (declaringGroup : GroupPath) (fieldSurfaces valueSurfaces : List SurfaceFieldPath) :
    Except ElabError (List FlatNumberField × List FlatNumberField) := do
  let fields ← elaborateNumberValueListOperands model declaringGroup fieldSurfaces
    .emptyValueListFields
  let values ← elaborateNumberValueListOperands model declaringGroup valueSurfaces
    .emptyValueListValueFields
  rejectDuplicateNumberValueListOperands (fields ++ values)
  pure (fields.map (·.2), values.map (·.2))

private def elaborateTextFieldOperand (model : FlatModel)
    (declaringGroup : GroupPath) : SurfaceTextFieldOperand →
      Except ElabError (List String × FlatTextFieldOperand × DirectComparableField)
  | .direct reference => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      match declaration.toTextFieldComparison? with
      | some (operand, profile) => pure (declaration.path, operand, profile)
      | none =>
          if declaration.isRawString then
            throw (.rawStringValue declaration.path)
          else
            throw (.textFieldOperandKindMismatch declaration.path
              declaration.policy.kind.surfaceKind)
  | surface@(.category _ _) => do
      let (path, _, operand) ←
        elaborateEnumerationFieldOperand model declaringGroup surface
      pure (path, .enumeration operand, .category)

private def elaborateCore (model : FlatModel) (declaringGroup : GroupPath) :
    SurfaceCondition → Except ElabError FlatCondition
  | .fieldFilled reference => do
      let declaration ← (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      pure (.fieldFilled declaration.toPresenceField)
  | .fieldNotFilled reference => do
      let declaration ← (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      pure (.fieldNotFilled declaration.toPresenceField)
  | .compareTextFields op leftReference rightReference => do
      let (leftPath, leftOperand, leftProfile) ←
        elaborateTextFieldOperand model declaringGroup leftReference
      let (rightPath, rightOperand, rightProfile) ←
        elaborateTextFieldOperand model declaringGroup rightReference
      finishTextFieldComparison op leftPath rightPath
        (leftOperand, leftProfile) (rightOperand, rightProfile)
  | .enumerationValueList quantifier surfaces values => do
      let operands ←
        elaborateEnumerationLiteralFieldList model declaringGroup surfaces values
      pure (.tokenValueList quantifier (operands.map .enumeration) (.literals values))
  | .enumerationFieldValueList quantifier fieldSurfaces valueSurfaces => do
      let (fields, values) ←
        elaborateEnumerationFieldValueSides model declaringGroup fieldSurfaces valueSurfaces
      pure (.tokenValueList quantifier (fields.map .enumeration)
        (.fields (values.map .enumeration)))
  | .stringValueList quantifier surfaces values => do
      let operands ←
        elaborateStringLiteralFieldList model declaringGroup surfaces values
      pure (.tokenValueList quantifier operands (.literals values))
  | .stringFieldValueList quantifier fieldSurfaces valueSurfaces => do
      let (fields, values) ←
        elaborateStringFieldValueSides model declaringGroup fieldSurfaces valueSurfaces
      pure (.tokenValueList quantifier fields (.fields values))
  | .stringValueMembership op surface values => do
      let operand ← elaborateStringLiteralList model declaringGroup surface values
      pure (.tokenValueList op.quantifier [operand] (.literals values))
  | .stringFieldValueMembership op surface valueSurfaces => do
      let (fields, values) ←
        elaborateStringFieldValueSides model declaringGroup [surface] valueSurfaces
      pure (.tokenValueList op.quantifier fields (.fields values))
  | .numberValueMembership op surface values => do
      let (operand, values) ←
        elaborateNumberLiteralMembership model declaringGroup surface values
      pure (.numberValueList op.quantifier [operand] (.literals values))
  | .numberFieldValueMembership op surface valueSurfaces => do
      let (fields, values) ←
        elaborateNumberFieldValueSides model declaringGroup [surface] valueSurfaces
      pure (.numberValueList op.quantifier fields (.fields values))
  | .numberFieldValueList quantifier fieldSurfaces valueSurfaces => do
      let (fields, values) ←
        elaborateNumberFieldValueSides model declaringGroup fieldSurfaces valueSurfaces
      pure (.numberValueList quantifier fields (.fields values))
  | .enumerationValueMembership op surface values => do
      let operand ←
        elaborateEnumerationLiteralList model declaringGroup surface values
      pure (.tokenValueList op.quantifier [.enumeration operand] (.literals values))
  | .enumerationFieldValueMembership op surface valueSurfaces => do
      let (fields, values) ←
        elaborateEnumerationFieldValueSides model declaringGroup [surface] valueSurfaces
      pure (.tokenValueList op.quantifier (fields.map .enumeration)
        (.fields (values.map .enumeration)))
  | .compareFields op leftReference rightReference => do
      let left ← (model.resolveNonrepeatableFieldUnchecked declaringGroup leftReference).mapError .resolve
      let right ← (model.resolveNonrepeatableFieldUnchecked declaringGroup rightReference).mapError .resolve
      if left.isRawString then
        throw (.rawStringValue left.path)
      else if right.isRawString then
        throw (.rawStringValue right.path)
      else match left.policy.kind, right.policy.kind with
      | .temporal leftKind leftComponents, .temporal rightKind rightComponents =>
          let comparison := op.toTemporal
          if comparison.admitsFormats model.hasBaseYear leftComponents rightComponents then
            pure (.compare (.temporal comparison
              (.fieldValue { id := left.id, kind := leftKind, components := leftComponents })
              (.fieldValue { id := right.id, kind := rightKind, components := rightComponents })))
          else
            throw (.temporalFormatsIncompatible left.path right.path)
      | leftKind, rightKind =>
          match left.toTextFieldComparison?, right.toTextFieldComparison? with
          | some (leftOperand, leftProfile), some (rightOperand, rightProfile) =>
              finishTextFieldComparison op left.path right.path
                (leftOperand, leftProfile) (rightOperand, rightProfile)
          | _, _ =>
              throw (.temporalOperandKindMismatch left.path right.path
                leftKind.surfaceKind rightKind.surfaceKind)
  | .compareToday op position reference => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      match declaration.policy.kind with
      | .temporal kind components =>
          let comparison := op.toTemporal
          if comparison.admitsToday model.hasBaseYear components then
            let field : FlatTemporalOperand :=
              .fieldValue {
                id := declaration.id
                kind := kind
                components := components }
            let today := FlatTemporalOperand.todayValue model.timeZoneId
            pure (temporalPointComparison comparison position today field)
          else
            match position with
            | .left =>
                throw (.temporalFormatsIncompatible ["<Today>"] declaration.path)
            | .right =>
                throw (.temporalFormatsIncompatible declaration.path ["<Today>"])
      | kind =>
          match position with
          | .left =>
              throw (.temporalOperandKindMismatch ["<Today>"] declaration.path
                (.temporal .date) kind.surfaceKind)
          | .right =>
              throw (.temporalOperandKindMismatch declaration.path ["<Today>"]
                kind.surfaceKind (.temporal .date))
  | .compareBaseYear op position reference => do
      let year ← match model.baseYear with
        | some year => pure year
        | none => throw .baseYearNotDeclared
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      match declaration.policy.kind with
      | .number info =>
          let fieldOp := match position with
            | .left => op.swapped
            | .right => op
          let numeric ← match fieldOp.toNumeric? with
            | some numeric => pure numeric
            | none => throw (.unsupportedOperator op)
          if numeric.acceptsScales (.field info.scale) (.field 0) then
            pure (.compare (.number (.ordinary numeric)
              { id := declaration.id, info } year))
          else
            throw (.baseYearScaleMismatch declaration.path info.scale)
      | .temporal kind components =>
          let comparison := op.toTemporal
          if comparison.admitsBaseYear components then
            let field : FlatTemporalOperand :=
              .fieldValue {
                id := declaration.id
                kind := kind
                components := components }
            let baseYear := FlatTemporalOperand.baseYearValue model.timeZoneId year
            pure (temporalPointComparison comparison position baseYear field)
          else
            match position with
            | .left =>
                throw (.temporalFormatsIncompatible ["<BaseYear>"] declaration.path)
            | .right =>
                throw (.temporalFormatsIncompatible declaration.path ["<BaseYear>"])
      | kind =>
          match position with
          | .left =>
              throw (.temporalOperandKindMismatch ["<BaseYear>"] declaration.path
                (.temporal .date) kind.surfaceKind)
          | .right =>
              throw (.temporalOperandKindMismatch declaration.path ["<BaseYear>"]
                kind.surfaceKind (.temporal .date))
  | .compareBaseYearRange op position endpoint reference => do
      let year ← match model.baseYear with
        | some year => pure year
        | none => throw .baseYearNotDeclared
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      let sourcePath := endpoint.surfacePath
      match declaration.policy.kind with
      | .temporal kind components =>
          let comparison := op.toTemporal
          if comparison.admitsFormats true components TemporalComponents.fullDate then
            let field : FlatTemporalOperand :=
              .fieldValue {
                id := declaration.id
                kind := kind
                components := components }
            let source : FlatTemporalOperand :=
              .baseYearRangeValue model.timeZoneId year endpoint
            pure (temporalPointComparison comparison position source field)
          else
            match position with
            | .left => throw (.temporalFormatsIncompatible sourcePath declaration.path)
            | .right => throw (.temporalFormatsIncompatible declaration.path sourcePath)
      | kind =>
          match position with
          | .left =>
              throw (.temporalOperandKindMismatch sourcePath declaration.path
                (.temporal .date) kind.surfaceKind)
          | .right =>
              throw (.temporalOperandKindMismatch declaration.path sourcePath
                kind.surfaceKind (.temporal .date))
  | .compareNow op position reference => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      match declaration.policy.kind with
      | .temporal kind components =>
          let comparison := op.toTemporal
          if !components.hasTime then
            throw (.temporalNowRequiresTime declaration.path)
          else if !comparison.admitsNow model.hasBaseYear components then
            match position with
            | .left =>
                throw (.temporalFormatsIncompatible ["<Now>"] declaration.path)
            | .right =>
                throw (.temporalFormatsIncompatible declaration.path ["<Now>"])
          else
            let field : FlatTemporalOperand :=
              .fieldValue {
                id := declaration.id
                kind := kind
                components := components }
            pure (temporalPointComparison comparison position .nowValue field)
      | kind =>
          match position with
          | .left =>
              throw (.temporalOperandKindMismatch ["<Now>"] declaration.path
                (.temporal .dateTime) kind.surfaceKind)
          | .right =>
              throw (.temporalOperandKindMismatch declaration.path ["<Now>"]
                kind.surfaceKind (.temporal .dateTime))
  | .compareEnumeration op reference projectionRef expected => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      elaborateEnumerationCore declaration op projectionRef expected
  | .compare op reference literal => do
      let declaration ← (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      match declaration.policy.kind with
      | .number info => do
          let numeric ← match op.toNumeric? with
            | some numeric => pure numeric
            | none => throw (.unsupportedOperator op)
          match literal with
          | .number expected =>
              pure (.compare (.number (.ordinary numeric)
                { id := declaration.id, info } expected))
          | literal =>
              throw (.literalKindMismatch declaration.path .number literal.kind)
      | .boolean => do
          let equality ← match op.toEquality? with
            | some equality => pure equality
            | none => throw (.unsupportedOperator op)
          match literal with
          | .boolean expected =>
              pure (.compare (.boolean equality { id := declaration.id } expected))
          | literal =>
              throw (.literalKindMismatch declaration.path .boolean literal.kind)
      | .confirm => do
          let equality ← match op.toEquality? with
            | some equality => pure equality
            | none => throw (.unsupportedOperator op)
          match literal with
          | .boolean expected =>
              if expected then
                pure (.compare (.confirm equality { id := declaration.id }))
              else
                throw (.illegalConfirmLiteral declaration.path)
          | literal =>
              throw (.literalKindMismatch declaration.path .confirm literal.kind)
      | .string => do
          let field ← requireStringValueField declaration
          let equality ← match op.toEquality? with
            | some equality => pure equality
            | none => throw (.unsupportedOperator op)
          match literal with
          | .string expected =>
              pure (.compare (.string equality field expected))
          | literal =>
              throw (.literalKindMismatch declaration.path .string literal.kind)
      | .enumeration =>
          match literal with
          | .string expected => elaborateEnumerationCore declaration op .stored expected
          | literal =>
              throw (.literalKindMismatch declaration.path .string literal.kind)
      | .temporal kind components =>
          match literal with
          | .date literalComponents instant =>
              let literalPath := ["<date-literal>"]
              if !literalComponents.isDateLiteral then
                throw (.invalidTemporalLiteralComponents literalPath)
              else if !literalComponents.year && !model.hasBaseYear then
                throw (.temporalLiteralNeedsBaseYear literalPath)
              else
                let comparison := op.toTemporal
                if comparison.admitsFormats model.hasBaseYear
                    components literalComponents then
                  pure (.compare (.temporal comparison
                    (.fieldValue {
                      id := declaration.id
                      kind := kind
                      components := components })
                    (.literalValue instant)))
                else
                  throw (.temporalFormatsIncompatible declaration.path literalPath)
          | literal =>
              throw (.literalKindMismatch declaration.path (.temporal kind) literal.kind)
  | .lengthCompare op reference expected => do
      let declaration ← (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      if declaration.isRawString then
        throw (.rawStringLength declaration.path)
      else
        let lengthOp ← match op.toStringLength? with
          | some lengthOp => pure lengthOp
          | none => throw (.unsupportedOperator op)
        match declaration.toStringValueField? with
        | some field => pure (.compare (.stringLength lengthOp field expected))
        | none => throw (.lengthOperandKindMismatch declaration.path
            declaration.policy.kind.surfaceKind)
  | .literalCompareLength expected op reference => do
      let declaration ← (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      if declaration.isRawString then
        throw (.rawStringLength declaration.path)
      else
        let lengthOp ← match op.swapped.toStringLength? with
          | some lengthOp => pure lengthOp
          | none => throw (.unsupportedOperator op)
        match declaration.toStringValueField? with
        | some field => pure (.compare (.stringLength lengthOp field expected))
        | none => throw (.lengthOperandKindMismatch declaration.path
            declaration.policy.kind.surfaceKind)
  | .and left right => do
      pure (.and (← elaborateCore model declaringGroup left)
        (← elaborateCore model declaringGroup right))
  | .or left right => do
      pure (.or (← elaborateCore model declaringGroup left)
        (← elaborateCore model declaringGroup right))

/-- Checked surface-to-core lowering. Later consumers receive the proof-bearing wrapper,
    not a caller-asserted field/policy pairing. -/
def elaborate (model : FlatModel) (declaringGroup : GroupPath)
    (condition : SurfaceCondition) : Except ElabError (CheckedFlatCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let core ← elaborateCore model declaringGroup condition
      core.checkAgainstValidatedModel model declaringGroup hModel

structure RawFlatContext where
  read : FieldId → RawCell

def malformedCheckedCell : CheckedCell :=
  { rawPresent := true, parsed := none, findings := [.malformed] }

/-- Compile one raw cell through declaration-owned scalar or ordinary closed-Enumeration admission. Registered custom Strings require their prepared overlay and fail closed here. -/
def FlatFieldDecl.checkRaw (declaration : FlatFieldDecl) (raw : RawCell) : CheckedCell :=
  match declaration.customType, declaration.policy.kind, declaration.enumeration with
  | some _, _, _ => malformedCheckedCell
  | none, .enumeration, some source =>
      match elaborateEnumeration source with
      | .ok checked => checked.checkRaw raw
      | .error _ => malformedCheckedCell
  | none, .enumeration, none => malformedCheckedCell
  | none, _, some _ => malformedCheckedCell
  | none, _, none => formalCheck declaration.policy raw

/-- Compile raw cells with the same unique declaration and policy used by elaboration.
    An invalid/unresolved identifier becomes malformed rather than acquiring a guessed
    default policy. -/
def FlatModel.checkContext (model : FlatModel) (raw : RawFlatContext) : FlatContext where
  read id :=
    match model.lookupUniqueId id with
    | .ok declaration => declaration.checkRaw (raw.read id)
    | .error _ => malformedCheckedCell

def elaborateAndEvalFull (model : FlatModel) (world : World) (declaringGroup : GroupPath)
    (raw : RawFlatContext) (hasContent : Bool) (condition : SurfaceCondition) :
    Except ElabError Verdict := do
  let checked ← elaborate model declaringGroup condition
  pure (checked.core.evalFull ((model.checkContext raw).withWorld world) hasContent)

end A12Kernel
