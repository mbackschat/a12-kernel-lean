import A12Kernel.Elaboration.GroupPresenceInput
import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.ComputationCondition

/-! # Checked-document projection for resolved group presence -/

namespace A12Kernel

/-- Resolve a computation group's two content constituents from model ownership. Deeper fields
need no cell read once their physical row already supplies content; fixed descendants stay local. -/
def FlatModel.computationGroupSource (model : FlatModel) (groupPath : GroupPath) :
    ResolvedComputationGroupSource :=
  let scope := model.repeatableScopeForGroupPath groupPath
  { scope
    fields := ((model.groupSubtreeFields groupPath).filter (·.repeatableScope == scope)).map (·.id)
    rowLevels := (model.repeatableGroups.filter (groupPath.isPrefixOf ·.path)).map (·.level) }

/-- Retain exact model-derived membership and content while binding the operand to the target row. -/
def ComputationGroupOperand.admitted (source : ComputationGroupOperand)
    (model : FlatModel) (scope : List RepeatableLevel) : Bool :=
  model.hasGroupPath source.reference.path &&
    source.content == model.computationGroupSource source.reference.path &&
    source.members == (model.groupSubtreeFields source.reference.path).map (·.id) &&
    source.reference.boundRepeatableScope == source.content.scope &&
    match source.starPath with
    | none => source.content.scope.isPrefixOf scope
    | some path =>
        model.repeatableAxesForScope? source.content.scope == some path.axes &&
          path.firstStar < path.axes.length && path.bindingScope.isPrefixOf scope

namespace CheckedDocument

/-- Specialize the model-owned slice calculation to a checked document and its later cell view. -/
def groupPresenceInputFromSlice (_checked : CheckedDocument model)
    (rows : List RowAddr) (cells : List CheckedCellPlacement)
    (groupPath : GroupPath) (environment : Env)
    (relevance : GroupRelevance) (structuralError : Bool)
    (silentErrorAddresses : List CellAddr := []) :
    Except CheckedGroupPresenceError ResolvedGroupPresenceInput :=
  model.groupPresenceInputFromSlice rows cells groupPath environment relevance structuralError silentErrorAddresses

/-- Derive one resolved validation-group slice using a later checked-cell placement view and every immutable source row. Full-validation and source-complete later views use this specialization. -/
def groupPresenceInputFromCells (checked : CheckedDocument model)
    (cells : List CheckedCellPlacement)
    (groupPath : GroupPath) (environment : Env)
    (relevance : GroupRelevance) (structuralError : Bool) :
    Except CheckedGroupPresenceError ResolvedGroupPresenceInput :=
  checked.groupPresenceInputFromSlice checked.source.instantiatedRows cells
    groupPath environment relevance structuralError

/-- Derive one resolved validation-group slice from the base checked document. Relevance and caller-supplied group errors remain explicit phase inputs; excess-row diagnostics do not enter ancestor cache-error state (spec/10 §5). -/
def groupPresenceInput (checked : CheckedDocument model)
    (groupPath : GroupPath) (environment : Env)
    (relevance : GroupRelevance) (structuralError : Bool) :
    Except CheckedGroupPresenceError ResolvedGroupPresenceInput :=
  checked.groupPresenceInputFromCells checked.checkedCells groupPath environment
    relevance structuralError

end CheckedDocument

end A12Kernel
