import A12Kernel.Semantics.FlatValidation

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
    the documented local → ancestor → model-wide lookup order. -/
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
  deriving Repr, DecidableEq

inductive SurfaceScalarKind where
  | number
  | boolean
  | confirm
  | string
  deriving Repr, DecidableEq

namespace SurfaceLiteral

def kind : SurfaceLiteral → SurfaceScalarKind
  | .number _ => .number
  | .boolean _ => .boolean
  | .string _ => .string

end SurfaceLiteral

inductive SurfaceCondition where
  | compare (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
      (literal : SurfaceLiteral)
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

def toFlatField (declaration : FlatFieldDecl) : FlatField :=
  match declaration.policy.kind with
  | .number info => .number { id := declaration.id, info }
  | .boolean => .boolean { id := declaration.id }
  | .confirm => .confirm { id := declaration.id }

end FlatFieldDecl

structure FlatModel where
  fields : List FlatFieldDecl
  fieldRefByShortNameAllowed : Bool := false
  deriving Repr, DecidableEq

inductive ResolveError where
  | invalidModelPath (path : List String)
  | duplicateFieldId (id : FieldId)
  | duplicateEntityPath (path : List String)
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
  | incoherentCore
  deriving Repr, DecidableEq

private def validName (name : String) : Bool := !name.isEmpty

private def validGroupPath (path : GroupPath) : Bool :=
  !path.isEmpty && path.all validName

private def FlatFieldDecl.hasValidPath (declaration : FlatFieldDecl) : Bool :=
  validGroupPath declaration.groupPath && validName declaration.name

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

/-- Unique lookup is intentionally order-independent: ambiguity is an error, never a
    first-match choice. -/
def FlatModel.lookupUniqueId (model : FlatModel) (id : FieldId) :
    Except ResolveError FlatFieldDecl :=
  match model.fields.filter (fun declaration => declaration.id == id) with
  | [] => .error (.unknownFieldId id)
  | [declaration] => .ok declaration
  | _ => .error (.duplicateFieldId id)

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

private def walkUp (group : GroupPath) (parents : Nat) : Except ResolveError GroupPath :=
  if parents < group.length then
    .ok (group.take (group.length - parents))
  else
    .error (.aboveRoot parents)

private def FlatFieldDecl.requireNonrepeatable (declaration : FlatFieldDecl) :
    Except ResolveError FlatFieldDecl :=
  if declaration.repeatableScope.isEmpty then
    .ok declaration
  else
    .error (.repeatableReference declaration.path)

/-- Resolve a bare single-segment reference exactly as the kernel parser does: try the
    declaring group, then (when enabled) require one model-wide short-name match. There
    is deliberately no implicit ancestor walk; parent lookup requires `..`. -/
private def FlatModel.resolveBare (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl := do
  match ← model.lookupPath? (declaringGroup ++ [reference.field]) with
  | some declaration => declaration.requireNonrepeatable
  | none =>
      if model.fieldRefByShortNameAllowed then
        match model.fields.filter (fun declaration => declaration.name == reference.field) with
        | [] => throw (.invalidEntity reference)
        | [declaration] => declaration.requireNonrepeatable
        | _ => throw (.shortNameNotUnique reference.field)
      else
        throw (.invalidEntity reference)

private def FlatModel.resolveFieldUnchecked (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FlatFieldDecl := do
  if !validGroupPath declaringGroup then throw (.invalidRuleGroup declaringGroup)
  if !reference.hasValidShape then throw (.invalidReference reference)
  match reference.base with
  | .absolute =>
      match ← model.lookupPath? (reference.groups ++ [reference.field]) with
      | some declaration => declaration.requireNonrepeatable
      | none => throw (.invalidEntity reference)
  | .relative parents =>
      if parents == 0 && reference.groups.isEmpty then
        model.resolveBare declaringGroup reference
      else
        let base ← walkUp declaringGroup parents
        match ← model.lookupPath? (base ++ reference.groups ++ [reference.field]) with
        | some declaration => declaration.requireNonrepeatable
        | none => throw (.invalidEntity reference)

/-- Resolve one structured field path against a validated expanded model. -/
def FlatModel.resolveField (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl := do
  model.validate
  model.resolveFieldUnchecked declaringGroup reference

private def FieldKind.surfaceKind : FieldKind → SurfaceScalarKind
  | .number _ => .number
  | .boolean => .boolean
  | .confirm => .confirm

private def SurfaceComparisonOp.toEquality? : SurfaceComparisonOp → Option EqualityOp
  | .equal => some .equal
  | .notEqual => some .notEqual
  | _ => none

private def FlatComparison.asField : FlatComparison → FlatField
  | .number _ field _ => .number field
  | .boolean _ field _ => .boolean field
  | .confirm _ field => .confirm field

def FlatField.matchesDecl (field : FlatField) (declaration : FlatFieldDecl) : Bool :=
  field == declaration.toFlatField

def FlatModel.admitsField (model : FlatModel) (field : FlatField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration => declaration.repeatableScope.isEmpty && field.matchesDecl declaration
  | .error _ => false

def FlatCondition.wellFormedBool (condition : FlatCondition) (model : FlatModel) : Bool :=
  match condition with
  | .compare comparison => model.admitsField comparison.asField
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

private def elaborateCore (model : FlatModel) (declaringGroup : GroupPath) :
    SurfaceCondition → Except ElabError FlatCondition
  | .fieldFilled reference => do
      let declaration ← (model.resolveFieldUnchecked declaringGroup reference).mapError .resolve
      pure (.fieldFilled declaration.toFlatField)
  | .fieldNotFilled reference => do
      let declaration ← (model.resolveFieldUnchecked declaringGroup reference).mapError .resolve
      pure (.fieldNotFilled declaration.toFlatField)
  | .compare op reference literal => do
      let equality ← match op.toEquality? with
        | some equality => pure equality
        | none => throw (.unsupportedOperator op)
      let declaration ← (model.resolveFieldUnchecked declaringGroup reference).mapError .resolve
      match declaration.policy.kind, literal with
      | .number info, .number expected =>
          pure (.compare (.number equality { id := declaration.id, info } expected))
      | .boolean, .boolean expected =>
          pure (.compare (.boolean equality { id := declaration.id } expected))
      | .confirm, .boolean true =>
          pure (.compare (.confirm equality { id := declaration.id }))
      | .confirm, .boolean false =>
          throw (.illegalConfirmLiteral declaration.path)
      | fieldKind, literal =>
          throw (.literalKindMismatch declaration.path fieldKind.surfaceKind literal.kind)
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
      if hCore : core.wellFormedBool model = true then
        pure {
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore
        }
      else
        throw .incoherentCore

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
