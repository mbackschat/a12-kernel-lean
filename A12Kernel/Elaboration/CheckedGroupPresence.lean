import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.GroupPresence

/-! # Checked-document projection for resolved group presence -/

namespace A12Kernel

inductive CheckedGroupPresenceError where
  | unknownGroup (path : GroupPath)
  | missingBinding (level : RepeatableLevel)
  | duplicateBinding (level : RepeatableLevel)
  | zeroBinding (level : RepeatableLevel)
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

/-- Derive one resolved validation-group slice from the checked document. Relevance and later structural findings remain explicit phase inputs. -/
def groupPresenceInput (checked : CheckedDocument model)
    (groupPath : GroupPath) (environment : Env)
    (relevance : GroupRelevance) (structuralError : Bool) :
    Except CheckedGroupPresenceError ResolvedGroupPresenceInput :=
  if !model.hasGroupPath groupPath then
    .error (.unknownGroup groupPath)
  else
    match pathForScope environment (model.repeatableScopeForGroupPath groupPath) with
    | .error error => .error error
    | .ok addressPrefix =>
        let descendantCells := checked.checkedCells.filterMap fun placement =>
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
          hasInstantiatedRow := checked.source.instantiatedRows.any
            (rowWithinGroup model groupPath addressPrefix)
          structuralError
          relevance
        }

end CheckedDocument

end A12Kernel
