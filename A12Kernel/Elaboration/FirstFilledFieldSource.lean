import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.CheckedStarShape
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.FilledFieldGroupCount
import A12Kernel.Elaboration.FilledFieldStarCount

/-! # Carrier-owned `FirstFilledValue` sources

Payload declarations determine carrier agreement, while key/index declarations remain scheduling
and eager formal-input dependencies. Selected entity lists bind against the computed target's scope;
legacy plain lists and sibling stars retain their established certificates. Source-order presence
and poison follow the common first-filled mechanism in `spec/07` §5 and selection in `spec/08` §4.
-/

namespace A12Kernel

/-- An authored `FirstFilledValue` source: one starred path or an entity list. -/
inductive SurfaceFirstFilledSource where
  | star (path : SurfaceStarFieldPath)
  | list (source : SurfaceFieldEntitySource)
  deriving Repr, DecidableEq

/-- Every cell the scan may reach, in authored order, and whether a star's declared extent runs past
its instantiated rows, which a token scan reads as an omitted tail; a list has none. -/
structure ResolvedFirstFilledSource where
  cells : List CheckedAddressedCell
  hasOpenTail : Bool

/-- Project selection poison through each carrier's existing result type. Structural faults remain
outside this projection and cannot be confused with a semantic clear. -/
def evaluateFirstFilledSource (result : Except FormalCause ResolvedFirstFilledSource)
    (poison : FormalCause → α) (scan : ResolvedFirstFilledSource → α) : α :=
  match result with
  | .error cause => poison cause
  | .ok resolved => scan resolved

/-- Stored scalar, ordinary extent and selected operands retain selection certificates separately from
payload declarations: index and key dependencies need not have the payload's kind (spec/08 §4).
Ordinary star and group slots retain their established extent certificates (spec/07 §5). -/
inductive FirstFilledFieldOperand (model : FlatModel) where
  | field (declaration : FlatFieldDecl)
  | indexed (source : CheckedSemanticIndexSource model)
  | keyed (source : CheckedKeyedEntityExtent model)
  | star (source : CheckedFilledFieldStarSource model)
  | group (source : CheckedFilledFieldCountGroupSource model)

namespace FirstFilledFieldOperand

def declarations : FirstFilledFieldOperand model → List FlatFieldDecl
  | .field declaration => [declaration]
  | .indexed source => [source.targetDeclaration]
  | .keyed source => source.declarations
  | .star source => [source.source.declaration]
  | .group source => source.declarations

def referencesWith (operand : FirstFilledFieldOperand model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  match operand with
  | .field declaration => declaration.id == field
  | .indexed source => source.referencesField field
  | .keyed source => source.referencesField field
  | .star source => source.source.declaration.id == field ||
      source.filter.any (fun having => filterReads having.condition)
  | .group source => source.declarations.any (·.id == field)

def referencesField (operand : FirstFilledFieldOperand model) (field : FieldId) : Bool :=
  operand.referencesWith field (·.referencesField field)

end FirstFilledFieldOperand

/-- Legacy star/direct lists and target-bound mixed lists share carrier-specific scans. -/
inductive FirstFilledFieldSource (model : FlatModel) where
  | star (source : CheckedStarFieldPath model)
  | list (fields : List FlatFieldDecl)
  | selected (operands : List (FirstFilledFieldOperand model))

namespace FirstFilledFieldSource

/-- Payload declarations alone determine carrier agreement. -/
def declarations : FirstFilledFieldSource model → List FlatFieldDecl
  | .star source => [source.declaration]
  | .list fields => fields
  | .selected operands => operands.flatMap (·.declarations)

def referencesWith (source : FirstFilledFieldSource model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  match source with
  | .selected operands => operands.any (·.referencesWith field filterReads)
  | source => source.declarations.any (·.id == field)

def referencesField (source : FirstFilledFieldSource model) (field : FieldId) : Bool :=
  source.referencesWith field (·.referencesField field)

/-- Selected lists have already passed the shared authored arity and binding gates. -/
def admittedShape : FirstFilledFieldSource model → Bool
  | .star source => source.isDirectSingleStar
  | .list fields => decide (2 ≤ fields.length) && fields.all (·.repeatableScope.isEmpty)
  | .selected _ => true

end FirstFilledFieldSource

inductive FirstFilledListElabError where
  | shape (cause : FieldEntityShapeElabError)
  | group (cause : FilledFieldCountGroupElabError)
  | having (cause : CorrelationElabError)
  | unsupportedOperand
  deriving Repr, DecidableEq

structure CheckedFirstFilledFieldList (model : FlatModel) (declaringGroup : GroupPath) where
  source : FirstFilledFieldSource model
  declaringGroupValid : GroupPath.isValid declaringGroup = true

/-- Resolve against the computed target's binding scope. Spec/07 §5 and spec/08 §4 use the
extent's declaration order; Having captures the target binding independently of lexical origin. -/
def elaborateFirstFilledFieldList (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (authored : SurfaceFieldEntitySource) :
    Except FirstFilledListElabError (CheckedFirstFilledFieldList model declaringGroup) := do
  let shape ← (elaborateFieldEntityShapeIn model declaringGroup
    (model.repeatableScopeForGroupPath writtenGroup) authored .manyRequired
    (some writtenGroup) writtenGroup).mapError .shape
  let group (source : CheckedEntityGroupSource model) :=
    (FirstFilledFieldOperand.group <$>
      CheckedFilledFieldCountGroupSource.ofResolved model source).mapError FirstFilledListElabError.group
  let operands ← shape.operands.mapM fun
    | .field declaration .stored => pure (FirstFilledFieldOperand.field declaration)
    | .indexed source .stored => pure (.indexed source)
    | .keyed source .stored => pure (.keyed source)
    | .star source .stored => pure (.star (.plain declaringGroup source))
    | .starHaving source having .stored =>
        (FirstFilledFieldOperand.star <$> CheckedFilledFieldStarSource.withHaving model
          declaringGroup writtenGroup source having writtenGroup).mapError .having
    | .group reference => group (.fixed reference)
    | .starredGroup source => group (.starred source)
    | .starredGroupPresence source => group (.starredPresence source)
    | _ => throw .unsupportedOperand
  if hValid : GroupPath.isValid declaringGroup = true then
    let fields := operands.filterMap fun | .field field => some field | _ => none
    let source := if fields.length == operands.length && fields.all (·.repeatableScope.isEmpty)
      then FirstFilledFieldSource.list fields else .selected operands
    pure { source, declaringGroupValid := hValid }
  else throw .unsupportedOperand

end A12Kernel
