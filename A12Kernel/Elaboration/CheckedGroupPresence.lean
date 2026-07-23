import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.GroupPresence

/-! # Checked-document projection for resolved group presence -/

namespace A12Kernel

inductive CheckedGroupPresenceError where
  | unknownGroup (path : GroupPath)
  | missingBinding (level : RepeatableLevel)
  | duplicateBinding (level : RepeatableLevel)
  | zeroBinding (level : RepeatableLevel)
  | incoherentRepeatableScope (scope : List RepeatableLevel)
  deriving Repr, DecidableEq

namespace CheckedDocument

private def bindingAt (environment : Env) (level : RepeatableLevel) :
    Except CheckedGroupPresenceError Nat :=
  match environment.filter fun binding => binding.1 == level with
  | [] => .error (.missingBinding level)
  | [(_, coordinate)] =>
      if coordinate == 0 then .error (.zeroBinding level) else .ok coordinate
  | _ => .error (.duplicateBinding level)

private def pathForScope (environment : Env) :
    List RepeatableLevel → Except CheckedGroupPresenceError (List Nat)
  | [] => pure []
  | level :: levels => do
      pure ((← bindingAt environment level) :: (← pathForScope environment levels))

private def NatPath.isPrefixOf : List Nat → List Nat → Bool
  | [], _ => true
  | _, [] => false
  | expected :: expectedRest, actual :: actualRest =>
      expected == actual && NatPath.isPrefixOf expectedRest actualRest

private def rowWithinGroup (model : FlatModel) (groupPath : GroupPath)
    (addressPrefix : List Nat) (row : RowAddr) : Bool :=
  match model.repeatableGroupAtLevel? row.group with
  | none => false
  | some group =>
      groupPath.isPrefixOf group.path && addressPrefix.isPrefixOf row.path

private def hasOverLimitRowWithin (model : FlatModel) (groupPath : GroupPath)
    (addressPrefix : List Nat) : List RowAddr →
    Except CheckedGroupPresenceError Bool
  | [] => pure false
  | row :: rows =>
      if rowWithinGroup model groupPath addressPrefix row then
        match model.repeatableGroupAtLevel? row.group with
        | none => throw (.incoherentRepeatableScope [row.group])
        | some group =>
            let scope := model.repeatableScopeForGroupPath group.path
            match model.addressOverLimit? scope row.path with
            | none => throw (.incoherentRepeatableScope scope)
            | some true => pure true
            | some false => hasOverLimitRowWithin model groupPath addressPrefix rows
      else
        hasOverLimitRowWithin model groupPath addressPrefix rows

private def resolveGroupPresenceScope (model : FlatModel)
    (rows : List RowAddr) (groupPath : GroupPath) (environment : Env) :
    Except CheckedGroupPresenceError (List Nat × Bool) := do
  let addressPrefix ←
    pathForScope environment (model.repeatableScopeForGroupPath groupPath)
  let overLimitRow ← hasOverLimitRowWithin model groupPath addressPrefix
    rows
  pure (addressPrefix, overLimitRow)

/-- Derive one resolved validation-group slice using call-selected rows and a later checked-cell placement view over the same immutable document. The supplied slice must retain base addresses and may add model-owned absent-cell findings. -/
def groupPresenceInputFromSlice (_checked : CheckedDocument model)
    (rows : List RowAddr) (cells : List CheckedCellPlacement)
    (groupPath : GroupPath) (environment : Env)
    (relevance : GroupRelevance) (structuralError : Bool) :
    Except CheckedGroupPresenceError ResolvedGroupPresenceInput :=
  if !model.hasGroupPath groupPath then
    .error (.unknownGroup groupPath)
  else
    match resolveGroupPresenceScope model rows groupPath environment with
    | .error error => .error error
    | .ok (addressPrefix, overLimitRow) =>
        let descendantCells := cells.filterMap fun placement =>
          match model.lookupUniqueId placement.address.field with
          | .ok declaration =>
              if groupPath.isPrefixOf declaration.groupPath &&
                  addressPrefix.isPrefixOf placement.address.path then
                some placement.cell
              else
                none
          | .error _ => none
        .ok {
          descendantCells
          hasInstantiatedRow := rows.any
            (rowWithinGroup model groupPath addressPrefix)
          structuralError := structuralError || overLimitRow
          relevance
        }

/-- Derive one resolved validation-group slice using a later checked-cell placement view and every immutable source row. Full-validation and source-complete later views use this specialization. -/
def groupPresenceInputFromCells (checked : CheckedDocument model)
    (cells : List CheckedCellPlacement)
    (groupPath : GroupPath) (environment : Env)
    (relevance : GroupRelevance) (structuralError : Bool) :
    Except CheckedGroupPresenceError ResolvedGroupPresenceInput :=
  checked.groupPresenceInputFromSlice checked.source.instantiatedRows cells
    groupPath environment relevance structuralError

/-- Derive one resolved validation-group slice from the base checked document. Relevance and later structural findings remain explicit phase inputs; base over-repetition is derived from immutable row topology. -/
def groupPresenceInput (checked : CheckedDocument model)
    (groupPath : GroupPath) (environment : Env)
    (relevance : GroupRelevance) (structuralError : Bool) :
    Except CheckedGroupPresenceError ResolvedGroupPresenceInput :=
  checked.groupPresenceInputFromCells checked.checkedCells groupPath environment
    relevance structuralError

end CheckedDocument

end A12Kernel
