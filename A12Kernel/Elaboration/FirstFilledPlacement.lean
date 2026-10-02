import A12Kernel.Elaboration.AddressedFirstFilledStar
import A12Kernel.Elaboration.FirstFilledFieldSource

/-! # Where a carrier-owned `FirstFilledValue` target sits

The carriers below the String and Enumeration entity lists read a direct star or a list of plain
fields. Their target sits in one of two places, and the placement stays split as measured
([`spec/09`](../../spec/09-computations.md) §1). A fixed target is unrestricted and runs once, at the
empty environment, over a direct single-level star or a list of at least two plain nonrepeatable
fields. A repeatable target lies at or below the declaring group, is no index field, and runs at every
instantiated row of its scope over one sibling single-axis star whose outer levels that row binds,
clearing an over-limit row. Each carrier keeps its own kind gate, cell reading and target policy.
-/

namespace A12Kernel

/-- How a checked target sits relative to its source. -/
inductive FirstFilledPlacement (model : FlatModel) (targetField : FieldId) (target : FlatFieldDecl) :
    FirstFilledFieldSource model → Type where
  | fixed {source : FirstFilledFieldSource model} (targetFixed : target.repeatableScope = [])
      (shape : source.admittedShape = true) : FirstFilledPlacement model targetField target source
  | rows {star : CheckedStarFieldPath model} (repeatable : CheckedAddressedRepeatableTarget model)
      (declares : repeatable.declaration = target)
      (placement : CheckedFirstFilledStarPlacement model targetField target star) :
      FirstFilledPlacement model targetField target (.star star)

inductive FirstFilledPlacementElabError where
  | target (cause : ResolveError)
  | repeatableTarget (cause : AddressedRepeatableTargetElabError)
  | source (cause : StarPathElabError)
  | list (cause : FirstFilledListElabError)
  /-- A list at a repeatable target, which no row measures on these carriers: this project's limit,
  claiming no class. -/
  | rowList (path : List String)
  | starPlacement (cause : AddressedFirstFilledStarPlacementElabError)
  | sourceShape (path : List String)
  deriving Repr, DecidableEq

/-- One target and source certified against the same model, placed. -/
structure CheckedFirstFilledSite (model : FlatModel) where
  private mk ::
  targetField : FieldId
  target : FlatFieldDecl
  targetOwned : model.lookupUniqueId targetField = .ok target
  source : FirstFilledFieldSource model
  /-- The group the computation is declared in, which a fixed target need not lie in. -/
  declaringGroup : GroupPath
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  placement : FirstFilledPlacement model targetField target source

/-- Place the target, then elaborate the source against it: a star from the declaring group, a list
at the target's group as on every measured computation carrier. -/
def checkFirstFilledSite (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except FirstFilledPlacementElabError (CheckedFirstFilledSite model) := do
  match hOwned : model.lookupUniqueId targetField with
  | .error cause => throw (.target cause)
  | .ok target =>
    if hFixed : target.repeatableScope = [] then
      match authored with
      | .star path =>
        match hStar : elaborateStarFieldPath model declaringGroup path with
        | .error cause => throw (.source cause)
        | .ok star =>
          if hShape : (FirstFilledFieldSource.star star).admittedShape = true then
            pure { targetField, target, targetOwned := hOwned, source := .star star, declaringGroup
                   declaringGroupValid := elaborateStarFieldPath_declaringGroupValid hStar
                   placement := .fixed hFixed hShape }
          else throw (.sourceShape star.declaration.path)
      | .list list =>
        let checked ← (elaborateFirstFilledFieldList model declaringGroup target.groupPath list).mapError
          .list
        if hShape : (FirstFilledFieldSource.list (model := model) checked.fields).admittedShape = true
        then
          pure { targetField, target, targetOwned := hOwned, source := .list checked.fields
                 declaringGroup, declaringGroupValid := checked.declaringGroupValid
                 placement := .fixed hFixed hShape }
        else throw (.sourceShape ((checked.fields.head?.map (·.path)).getD target.path))
    else
      let repeatable ← (checkAddressedRepeatableTarget model declaringGroup targetField).mapError
        .repeatableTarget
      match authored with
      | .list _ => throw (.rowList target.path)
      | .star path =>
        match hStar : elaborateStarFieldPath model declaringGroup path with
        | .error cause => throw (.source cause)
        | .ok star =>
        if hDeclares : repeatable.declaration = target then
          let placement ← (checkFirstFilledStarPlacement targetField target hOwned
            (by intro empty; exact hFixed empty) star).mapError .starPlacement
          pure { targetField, target, targetOwned := hOwned, source := .star star, declaringGroup
                 declaringGroupValid := elaborateStarFieldPath_declaringGroupValid hStar
                 placement := .rows repeatable hDeclares placement }
        -- The repeatable-target certificate looked the same field up, so its declaration is this one.
        else throw (.target (.invalidRuleGroup declaringGroup))

namespace FirstFilledFieldSource

/-- Read a star's in-capacity rows below `environment`, or each listed field at it. -/
def resolveAt (source : FirstFilledFieldSource model) (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (environment : Env) :
    Except CheckedStarDocumentError ResolvedFirstFilledSource :=
  match source with
  | .star path => do
      let resolved ← path.resolveCheckedFieldWithRead input read environment
      pure { cells := resolved.cells, hasOpenTail := resolved.topology.domain.hasOpenTail }
  | .list fields => do
      let cells ← fields.mapM fun declaration =>
        input.addressedCellWithRead read environment declaration.id
      pure { cells, hasOpenTail := false }

end FirstFilledFieldSource

/-- A structural failure of a placed carrier's run: its target rows, a row's address, or a reached
source read. -/
inductive FirstFilledSiteFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

namespace CheckedFirstFilledSite

def referencesField (site : CheckedFirstFilledSite model) (field : FieldId) : Bool :=
  site.source.referencesField field

/-- Run `produce` at every target instance through the shared instance runner, each at its exact
target address. -/
def instances {Outcome Fault : Type} (site : CheckedFirstFilledSite model)
    (input : CheckedDocument model) (onRowError : ActualRowEnvironmentError → Fault)
    (onEnvironment : EnvBindingError → Fault)
    (clearOnly produce : CellAddr → Env → Except Fault Outcome) : Except Fault (List Outcome) :=
  let addressed (run : CellAddr → Env → Except Fault Outcome) (environment : Env) := do
    let path ← (environment.pathForScope site.target.repeatableScope).mapError onEnvironment
    run { field := site.targetField, path } environment
  input.computationTargetOutcomes site.target.repeatableScope onRowError (addressed clearOnly)
    (addressed produce)

end CheckedFirstFilledSite

end A12Kernel
