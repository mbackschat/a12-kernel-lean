import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.TemporalFormat

/-! # A12Kernel.Elaboration.Flat — checked lowering into the flat core

This capsule starts from structured, parser-independent surface paths and conditions. It
resolves absolute, parent-relative, and bare field references against an expanded flat
model, rejects unsupported or ambiguous input, and lowers accepted conditions into the
existing typed non-repeatable core. Quoting, named-ancestor labels, stars, semantic
indices, concrete EN/DE syntax, and repeatable evaluation remain outside this fragment.
-/

namespace A12Kernel

abbrev GroupPath := List String

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

inductive SurfaceComparisonOp where
  | equal
  | notEqual
  | less
  | lessEqual
  | greater
  | greaterEqual
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
  | temporal (kind : TemporalKind)
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
  | lengthCompare (op : SurfaceComparisonOp) (field : SurfaceFieldPath) (literal : Rat)
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
  repeatableScope : List RepeatableLevel := []
  deriving Repr, DecidableEq

namespace FlatFieldDecl

def path (declaration : FlatFieldDecl) : List String :=
  declaration.groupPath ++ [declaration.name]

/-- Convert one expanded declaration to the shared resolved Number-field representation. -/
def toNumberField? (declaration : FlatFieldDecl) : Option FlatNumberField :=
  match declaration.policy.kind with
  | .number info => some { id := declaration.id, info }
  | .boolean | .confirm | .string | .temporal _ _ => none

def toPresenceField (declaration : FlatFieldDecl) : FlatField :=
  match declaration.policy.kind with
  | .number info => .number { id := declaration.id, info }
  | .boolean => .boolean { id := declaration.id }
  | .confirm => .confirm { id := declaration.id }
  | .string => .string { id := declaration.id }
  | .temporal kind components =>
      .temporal { id := declaration.id, kind, components }

end FlatFieldDecl

/-- One repeatable model level with the exact group path on which `*` may be written. A field's `repeatableScope` alone cannot identify that path segment. -/
structure RepeatableGroupDecl where
  level : RepeatableLevel
  path : GroupPath
  deriving Repr, DecidableEq

structure FlatModel where
  fields : List FlatFieldDecl
  repeatableGroups : List RepeatableGroupDecl := []
  fieldRefByShortNameAllowed : Bool := false
  hasBaseYear : Bool := false
  deriving Repr, DecidableEq

inductive ResolveError where
  | invalidModelPath (path : List String)
  | duplicateFieldId (id : FieldId)
  | duplicateEntityPath (path : List String)
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
  | temporalLiteralNeedsBaseYear (path : List String)
  | invalidTemporalLiteralComponents (path : List String)
  | lengthOperandKindMismatch (path : List String) (actual : SurfaceScalarKind)
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

def FlatField.matchesDecl (field : FlatField) (declaration : FlatFieldDecl) : Bool :=
  declaration.toPresenceField == field

def FlatModel.admitsField (model : FlatModel) (field : FlatField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration => declaration.repeatableScope.isEmpty && field.matchesDecl declaration
  | .error _ => false

def FlatModel.admitsComparison (model : FlatModel) (comparison : FlatComparison) : Bool :=
  !comparison.fields.isEmpty && comparison.fields.all model.admitsField

def FlatCondition.wellFormedBool (condition : FlatCondition) (model : FlatModel) : Bool :=
  match condition with
  | .compare comparison => model.admitsComparison comparison
  | .fieldFilled field => model.admitsField field
  | .fieldNotFilled field => model.admitsField field
  | .and left right => left.wellFormedBool model && right.wellFormedBool model
  | .or left right => left.wellFormedBool model && right.wellFormedBool model

def FlatCondition.WellFormed (condition : FlatCondition) (model : FlatModel) : Prop :=
  condition.wellFormedBool model = true

/-- The only source-to-core result accepted by later stages. -/
structure CheckedFlatCondition (model : FlatModel) where
  core : FlatCondition
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model

/-- Certify a constructed core condition against an already-validated model. This is the shared boundary for ordinary surface lowering and semantic desugarings. -/
def FlatCondition.checkAgainstValidatedModel (condition : FlatCondition)
    (model : FlatModel) (modelValid : model.validate = .ok ()) :
    Except ElabError (CheckedFlatCondition model) :=
  if hCore : condition.wellFormedBool model = true then
    .ok {
      core := condition
      modelWellFormed := by
        rw [modelValid]
        rfl
      wellFormed := hCore
    }
  else
    .error .incoherentCore

private def elaborateCore (model : FlatModel) (declaringGroup : GroupPath) :
    SurfaceCondition → Except ElabError FlatCondition
  | .fieldFilled reference => do
      let declaration ← (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      pure (.fieldFilled declaration.toPresenceField)
  | .fieldNotFilled reference => do
      let declaration ← (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      pure (.fieldNotFilled declaration.toPresenceField)
  | .compareFields op leftReference rightReference => do
      let left ← (model.resolveNonrepeatableFieldUnchecked declaringGroup leftReference).mapError .resolve
      let right ← (model.resolveNonrepeatableFieldUnchecked declaringGroup rightReference).mapError .resolve
      match left.policy.kind, right.policy.kind with
      | .temporal leftKind leftComponents, .temporal rightKind rightComponents =>
          let comparison := op.toTemporal
          if comparison.admitsFormats model.hasBaseYear leftComponents rightComponents then
            pure (.compare (.temporal comparison
              (.fieldValue { id := left.id, kind := leftKind, components := leftComponents })
              (.fieldValue { id := right.id, kind := rightKind, components := rightComponents })))
          else
            throw (.temporalFormatsIncompatible left.path right.path)
      | leftKind, rightKind =>
          throw (.temporalOperandKindMismatch left.path right.path
            leftKind.surfaceKind rightKind.surfaceKind)
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
          let equality ← match op.toEquality? with
            | some equality => pure equality
            | none => throw (.unsupportedOperator op)
          match literal with
          | .string expected =>
              pure (.compare (.string equality { id := declaration.id } expected))
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
      let lengthOp ← match op.toStringLength? with
        | some lengthOp => pure lengthOp
        | none => throw (.unsupportedOperator op)
      let declaration ← (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      match declaration.policy.kind with
      | .string => pure (.compare (.stringLength lengthOp { id := declaration.id } expected))
      | fieldKind => throw (.lengthOperandKindMismatch declaration.path fieldKind.surfaceKind)
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
      core.checkAgainstValidatedModel model hModel

structure RawFlatContext where
  read : FieldId → RawCell

def malformedCheckedCell : CheckedCell :=
  { rawPresent := true, parsed := none, findings := [.malformed] }

/-- Compile raw cells with the same unique declaration and policy used by elaboration.
    An invalid/unresolved identifier becomes malformed rather than acquiring a guessed
    default policy. -/
def FlatModel.checkContext (model : FlatModel) (raw : RawFlatContext) : FlatContext where
  read id :=
    match model.lookupUniqueId id with
    | .ok declaration => formalCheck declaration.policy (raw.read id)
    | .error _ => malformedCheckedCell

def elaborateAndEvalFull (model : FlatModel) (declaringGroup : GroupPath)
    (raw : RawFlatContext) (hasContent : Bool) (condition : SurfaceCondition) :
    Except ElabError Verdict := do
  let checked ← elaborate model declaringGroup condition
  pure (checked.core.evalFull (model.checkContext raw) hasContent)

end A12Kernel
