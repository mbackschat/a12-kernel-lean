import A12Kernel.Elaboration.CheckedCellPlacement
import A12Kernel.Elaboration.Flat.Capacity
import A12Kernel.Semantics.GroupPresence

namespace A12Kernel

inductive CheckedGroupPresenceError where
  | unknownGroup (path : GroupPath)
  | missingBinding (level : RepeatableLevel)
  | duplicateBinding (level : RepeatableLevel)
  | zeroBinding (level : RepeatableLevel)
  | incoherentRepeatableScope (scope : List RepeatableLevel)
  deriving Repr, DecidableEq

namespace CheckedDocument

private def CheckedGroupPresenceError.ofEnvBinding : EnvBindingError →
    CheckedGroupPresenceError
  | .missingBinding level => .missingBinding level
  | .duplicateBinding level => .duplicateBinding level
  | .zeroBinding level => .zeroBinding level

private def NatPath.isPrefixOf : List Nat → List Nat → Bool
  | [], _ => true
  | _, [] => false
  | expected :: expectedRest, actual :: actualRest =>
      expected == actual && NatPath.isPrefixOf expectedRest actualRest

/-- Whether one instantiated row lies inside a group's subtree, at a bound outer address.

    The row-containment half of group content, and the rule both arms answer: the compute arm's
    group-count operand reaches the same decision through its own repeatable-descendant shape, and
    `groupCount_rowConstituent_eq_validationArm` states that agreement. Containment is by path
    prefix and carries no repetition-depth bound, which is what the Kernel was measured to do
    ([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-deep-repeatable-descendant-group-count)). Public because
    that cross-arm law needs it, not because callers outside this module should re-decide it. -/
def rowWithinGroup (model : FlatModel) (groupPath : GroupPath)
    (addressPrefix : List Nat) (row : RowAddr) : Bool :=
  match model.repeatableGroupAtLevel? row.group with
  | none => false
  | some group =>
      groupPath.isPrefixOf group.path && addressPrefix.isPrefixOf row.path

private def resolveGroupPresenceScope (model : FlatModel)
    (groupPath : GroupPath) (environment : Env) :
    Except CheckedGroupPresenceError (List Nat) :=
  (environment.pathForScope (model.repeatableScopeForGroupPath groupPath))
    |>.mapError CheckedGroupPresenceError.ofEnvBinding

end CheckedDocument

/-- Derive one resolved validation-group slice using call-selected rows and a later checked-cell placement view over the same immutable document. The supplied slice must retain base addresses and may add model-owned absent-cell findings. -/
def FlatModel.groupPresenceInputFromSlice (model : FlatModel)
    (rows : List RowAddr) (cells : List CheckedCellPlacement)
    (groupPath : GroupPath) (environment : Env)
    (relevance : GroupRelevance) (structuralError : Bool)
    (silentErrorAddresses : List CellAddr := []) :
    Except CheckedGroupPresenceError ResolvedGroupPresenceInput :=
  if !model.hasGroupPath groupPath then
    .error (.unknownGroup groupPath)
  else
    match CheckedDocument.resolveGroupPresenceScope model groupPath environment with
    | .error error => .error error
    | .ok addressPrefix =>
        let descendantCells := cells.filterMap fun placement =>
          match model.lookupUniqueId placement.address.field with
          | .ok declaration =>
              -- Capacity-invalid entries report structural findings before cache admission;
              -- they do not mark ancestor groups erroneous (CheckCommand's index-admission gate, spec/10 §5).
              if groupPath.isPrefixOf declaration.groupPath &&
                  addressPrefix.isPrefixOf placement.address.path &&
                  model.addressOverLimit? declaration.repeatableScope placement.address.path == some false then
                some placement.cell
              else
                none
          | .error _ => none
        let silentError := silentErrorAddresses.any fun address =>
          match model.lookupUniqueId address.field with
          | .ok declaration =>
              groupPath.isPrefixOf declaration.groupPath &&
                addressPrefix.isPrefixOf address.path &&
                model.addressOverLimit? declaration.repeatableScope address.path == some false
          | .error _ => false
        .ok {
          descendantCells
          hasInstantiatedRow := rows.any
            (CheckedDocument.rowWithinGroup model groupPath addressPrefix)
          structuralError
          silentError
          relevance
        }

end A12Kernel
