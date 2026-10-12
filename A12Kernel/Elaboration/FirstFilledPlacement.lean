import A12Kernel.Elaboration.AddressedFirstFilledStar
import A12Kernel.Elaboration.FirstFilledFieldSource
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Placement and reached reads for carrier-owned `FirstFilledValue`

Fixed targets run once. Repeatable targets retain the shared placement certificate and run at each
instantiated target row, clearing over-limit rows. Legacy sibling stars and target-bound selected
lists retain separate admission certificates; each carrier owns its kind gate and target policy.
Selected lists stop before resolving later operands once a value or poison settles the result
(`spec/07` §5, `spec/08` §4 and `spec/09` §1).
-/

namespace A12Kernel

/-- How a checked target sits relative to its source. -/
inductive FirstFilledPlacement (model : FlatModel) (targetField : FieldId) (target : FlatFieldDecl) :
    FirstFilledFieldSource model → Type where
  | fixed {source : FirstFilledFieldSource model} (targetFixed : target.repeatableScope = [])
      (shape : source.admittedShape = true) : FirstFilledPlacement model targetField target source
  | selectedRows {operands : List (FirstFilledFieldOperand model)}
      (repeatable : CheckedAddressedRepeatableTarget model)
      (declares : repeatable.declaration = target) :
      FirstFilledPlacement model targetField target (.selected operands)
  | rows {star : CheckedStarFieldPath model} (repeatable : CheckedAddressedRepeatableTarget model)
      (declares : repeatable.declaration = target)
      (placement : CheckedFirstFilledStarPlacement model targetField target star) :
      FirstFilledPlacement model targetField target (.star star)

inductive FirstFilledPlacementElabError where
  | target (cause : ResolveError)
  | repeatableTarget (cause : AddressedRepeatableTargetElabError)
  | source (cause : StarPathElabError)
  | list (cause : FirstFilledListElabError)
  /-- An unsupported row-list representation, without an asserted kernel diagnostic. -/
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
        if hShape : checked.source.admittedShape = true
        then
          pure { targetField, target, targetOwned := hOwned, source := checked.source
                 declaringGroup, declaringGroupValid := checked.declaringGroupValid
                 placement := .fixed hFixed hShape }
        else throw (.sourceShape ((checked.source.declarations.head?.map (·.path)).getD target.path))
    else
      match hRepeatable : checkAddressedRepeatableTarget model declaringGroup targetField with
      | .error cause => throw (.repeatableTarget cause)
      | .ok repeatable =>
      have hDeclares : repeatable.declaration = target := by
        have looked := repeatable.owned
        rw [checkAddressedRepeatableTarget_targetField hRepeatable, hOwned] at looked
        exact (Except.ok.inj looked).symm
      match authored with
      | .list list =>
        let checked ← (elaborateFirstFilledFieldList model declaringGroup target.groupPath list).mapError .list
        match checked.source with
        | .selected operands =>
          pure { targetField, target, targetOwned := hOwned, source := .selected operands, declaringGroup
                 declaringGroupValid := checked.declaringGroupValid
                 placement := .selectedRows repeatable hDeclares }
        | .list fields =>
          pure { targetField, target, targetOwned := hOwned,
                 source := .selected (fields.map FirstFilledFieldOperand.field), declaringGroup
                 declaringGroupValid := checked.declaringGroupValid
                 placement := .selectedRows repeatable hDeclares }
        | .star _ => throw (.rowList target.path)
      | .star path =>
        match hStar : elaborateStarFieldPath model declaringGroup path with
        | .error cause => throw (.source cause)
        | .ok star =>
          let placement ← (checkFirstFilledStarPlacement targetField target hOwned
            (by intro empty; exact hFixed empty) star).mapError .starPlacement
          pure { targetField, target, targetOwned := hOwned, source := .star star, declaringGroup
                 declaringGroupValid := elaborateStarFieldPath_declaringGroupValid hStar
                 placement := .rows repeatable hDeclares placement }

namespace FirstFilledFieldSource

/-- Stop at the first present or formally invalid cell, before any later callback or selection.
The source runtime's FirstValueCombiner stops on presence, including Boolean false (spec/07 §5). -/
private def scanCells (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (field : FieldId) :
    List Env → Except CheckedAddressingError (Option CheckedAddressedCell)
  | [] => pure none
  | environment :: remaining => do
      let cell ← input.addressedCellWithRead read environment field
      match observeCell .computation cell.cell with
      | .empty => scanCells input read field remaining
      | _ => pure (some cell)

/-- A callback failure on the current key is structural, just like a reached payload read; the
pure key-classification callback must not collapse it to a malformed cell. -/
private def selectedEnvironment (source : CheckedSemanticIndexSource model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (outer : Env) : Except CheckedAddressingError (CellObservation Env) := do
  let column ← input.resolveSemanticIndexColumnWith read source.group source.indexDeclaration.id outer
  let (cell, stored) ← match source.key with
    | .literal _ _ => pure (malformedCheckedCell, none)
    | .field declaration => do
        let address ← input.cellAddress outer declaration.id
        let cell ← (read address).mapError .document
        pure (cell, input.storedTextForCell address cell)
  source.selectEnvironmentWith .computation (fun _ _ _ => pure column) outer
    (fun _ => cell) (fun _ => stored)

private def scanFieldRows (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    List (FlatFieldDecl × Env) → Except CheckedAddressingError (Option CheckedAddressedCell)
  | [] => pure none
  | (declaration, environment) :: rest => do
      match ← scanCells input read declaration.id [environment] with
      | some cell => pure (some cell)
      | none => scanFieldRows input read rest

def resolveOperandAt (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (outer : Env)
    (operand : FirstFilledFieldOperand model) (world : Option World := none) :
      Except CheckedAddressingError (Except FormalCause (Option CheckedAddressedCell)) :=
  match operand with
  | .field declaration => Except.ok <$> scanCells input read declaration.id [outer]
  | .star source => do
      let resolved ← (source.source.path.resolveInCapacity input.source.toDocument outer).mapError .addressing
      match source.filter with
      | none => Except.ok <$> scanCells input read source.source.declaration.id resolved.environments
      | some having => do
          let read := input.filterReadWith read
          let candidates ← source.source.filterEnvironments input outer false
          let result ← having.condition.scanComputationResolving
            (input.resolvingCorrelationContextWithRead read world) outer
            (fun (_ : Unit) environment => do
              match ← scanCells input read source.source.declaration.id [environment] with
              | none => pure (.inl ())
              | some cell => pure (.inr cell)) candidates ()
          pure (match result with
            | .exhausted _ => .ok none
            | .terminated cell => .ok (some cell)
            | .poison cause => .error cause)
  | .group source => do
      let rows ← (model.groupOperandRows input.source.toDocument outer
        source.source.boundLevelCount source.declarations (·.repeatableScope)).mapError .addressing
      Except.ok <$> scanFieldRows input read rows
  | .indexed source => do
      let selected ← selectedEnvironment source input read outer
      match selected with
      | .empty => pure (.ok none)
      | .unknown cause | .poison cause => pure (.error cause)
      | .value environment => Except.ok <$> scanCells input read source.targetDeclaration.id [environment]
  | .keyed source => do
      let selected ← selectedEnvironment source.selection.indexSource input read outer
      match selected with
      | .empty => pure (.ok none)
      | .unknown cause | .poison cause => pure (.error cause)
      | .value environment =>
        let rows ← (source.rows input.source.toDocument environment).mapError .addressing
        Except.ok <$> scanFieldRows input read
          (rows.flatMap fun (declaration, environments, _) => environments.map (declaration, ·))

private def selectedOperands (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (outer : Env) (world : Option World) :
    List (FirstFilledFieldOperand model) →
      Except CheckedAddressingError (Except FormalCause ResolvedFirstFilledSource)
  | [] => pure (.ok { cells := [], hasOpenTail := false })
  | operand :: rest => do
      match ← resolveOperandAt input read outer operand world with
      | .error cause => pure (.error cause)
      | .ok (some cell) => pure (.ok { cells := [cell], hasOpenTail := false })
      | .ok none => selectedOperands input read outer world rest

/-- Keep structural addressing faults separate from semantic selection poison. Legacy sources
retain their read boundary; selected operands resolve only while the first-filled result is open. -/
def resolveAt (source : FirstFilledFieldSource model) (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (environment : Env)
    (world : Option World := none) :
    Except CheckedStarDocumentError (Except FormalCause ResolvedFirstFilledSource) :=
  match source with
  | .star path => do
      let resolved ← path.resolveCheckedFieldWithRead input read environment
      pure (.ok { cells := resolved.cells, hasOpenTail := resolved.topology.domain.hasOpenTail })
  | .list fields => do
      let cells ← fields.mapM fun declaration =>
        input.addressedCellWithRead read environment declaration.id
      pure (.ok { cells, hasOpenTail := false })
  | .selected operands => selectedOperands input read environment world operands

/-- Once one reached operand returns a cell, later operands cannot change the result or raise a
structural fault. The carrier subsequently distinguishes the cell's value from formal poison. -/
theorem resolveAt_selected_firstDecides
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (outer : Env) (operand : FirstFilledFieldOperand model) (rest : List (FirstFilledFieldOperand model)) (world : Option World := none)
    (cell : CheckedAddressedCell)
    (decides : resolveOperandAt input read outer operand world = .ok (.ok (some cell))) :
    (FirstFilledFieldSource.selected (operand :: rest)).resolveAt input read outer world =
      .ok (.ok { cells := [cell], hasOpenTail := false }) := by
  simp [resolveAt, selectedOperands, decides]
  rfl

/-- Selection poison is terminal before the next authored operand, including a usable fallback. -/
theorem resolveAt_selected_poisonStops
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (outer : Env) (operand : FirstFilledFieldOperand model) (rest : List (FirstFilledFieldOperand model)) (world : Option World := none)
    (cause : FormalCause)
    (poison : resolveOperandAt input read outer operand world = .ok (.error cause)) :
    (FirstFilledFieldSource.selected (operand :: rest)).resolveAt input read outer world = .ok (.error cause) := by
  simp [resolveAt, selectedOperands, poison]
  rfl

end FirstFilledFieldSource

/-- A structural failure of a placed carrier's run: its target rows, a row's address, or a reached
source read. -/
inductive FirstFilledSiteFault where
  | targetCheck (cause : StringComputationFault)
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

namespace CheckedFirstFilledSite

def referencesWith (site : CheckedFirstFilledSite model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  site.source.referencesWith field filterReads

def referencesField (site : CheckedFirstFilledSite model) (field : FieldId) : Bool :=
  site.referencesWith field (·.referencesField field)

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

/-- Bind every source declaration and the computed target to the shared eager inventory. -/
def formalInputPlan (site : CheckedFirstFilledSite model) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  checkImplicitGuardFormalInputPlan model
    ((model.fields.filter (fun declaration => site.referencesField declaration.id)).map (·.id))
    [site.targetField]

end CheckedFirstFilledSite

end A12Kernel
