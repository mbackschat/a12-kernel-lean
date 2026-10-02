import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.CheckedStarShape
import A12Kernel.Elaboration.FieldEntityList

/-! # The source of a fixed-target `FirstFilledValue`

A fixed-target `FirstFilledValue` reads one direct single-level star or a direct list of plain
nonrepeatable fields, and both feed the same ordered scan over checked cells. On a list the Kernel
selects the first filled cell, lets an empty one fall through and ends the scan at a malformed one,
measured on Boolean, DateFragment, Time and DateTime
([four-carrier checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-first-filled-formal-branch-four-carriers)).
Each carrier keeps its own kind gate over the source's declarations; this module owns only the shape
and the read.
-/

namespace A12Kernel

/-- An authored fixed-target `FirstFilledValue` source: one starred path or an entity list. -/
inductive SurfaceFirstFilledSource where
  | star (path : SurfaceStarFieldPath)
  | list (source : SurfaceFieldEntitySource)
  deriving Repr, DecidableEq

/-- Every cell the scan may reach, in authored order, and whether a star's declared extent runs past
its instantiated rows, which a token scan reads as an omitted tail; a list has none. -/
structure ResolvedFirstFilledSource where
  cells : List CheckedAddressedCell
  hasOpenTail : Bool

/-- A checked fixed-target `FirstFilledValue` source. -/
inductive FirstFilledFieldSource (model : FlatModel) where
  | star (source : CheckedStarFieldPath model)
  | list (fields : List FlatFieldDecl)

namespace FirstFilledFieldSource

/-- The declarations the source reads, in authored order. -/
def declarations : FirstFilledFieldSource model → List FlatFieldDecl
  | .star source => [source.declaration]
  | .list fields => fields

def referencesField (source : FirstFilledFieldSource model) (field : FieldId) : Bool :=
  source.declarations.any (·.id == field)

/-- The shapes this source admits: a direct single-level star, or a list of at least two plain
nonrepeatable fields. -/
def admittedShape : FirstFilledFieldSource model → Bool
  | .star source => source.isDirectSingleStar
  | .list fields => decide (2 ≤ fields.length) && fields.all (·.repeatableScope.isEmpty)

/-- Read a star's rows, or each listed field once. -/
def resolve (source : FirstFilledFieldSource model) (input : CheckedDocument model) :
    Except CheckedStarDocumentError ResolvedFirstFilledSource :=
  match source with
  | .star path => do
      let resolved ← path.resolveCheckedField input []
      pure { cells := resolved.cells, hasOpenTail := resolved.topology.domain.hasOpenTail }
  | .list fields => do
      let cells ← fields.mapM fun declaration =>
        input.addressedCellWithRead input.read [] declaration.id
      pure { cells, hasOpenTail := false }

end FirstFilledFieldSource

/-- Why an authored list source is refused. The shape's own classes are the shared entity list's; an
operand other than a plain stored field is this source's representation limit and claims no class. A
field under a repeatable group never reaches this reading: resolved with no bound level, the shared
shape refuses it as an unbound operand level first. -/
inductive FirstFilledListElabError where
  | shape (cause : FieldEntityShapeElabError)
  | unsupportedOperand
  deriving Repr, DecidableEq

/-- An authored list's plain fields, with the validity of the declaring group its shape resolved in. -/
structure CheckedFirstFilledFieldList (declaringGroup : GroupPath) where
  fields : List FlatFieldDecl
  declaringGroupValid : GroupPath.isValid declaringGroup = true

/-- Resolve an authored list through the shared entity-list shape, keeping its plain fields. -/
def elaborateFirstFilledFieldList (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (authored : SurfaceFieldEntitySource) :
    Except FirstFilledListElabError (CheckedFirstFilledFieldList declaringGroup) :=
  match hShape : elaborateFieldEntityShape model declaringGroup authored
      (writtenGroup := writtenGroup) with
  | .error cause => .error (.shape cause)
  | .ok shape => do
      let fields ← shape.operands.mapM fun
        | .field declaration .stored => pure declaration
        | _ => throw .unsupportedOperand
      pure { fields, declaringGroupValid := elaborateFieldEntityShape_declaringGroupValid hShape }

end A12Kernel
