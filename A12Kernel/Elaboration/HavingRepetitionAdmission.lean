import A12Kernel.Elaboration.HavingEntityList
import A12Kernel.Elaboration.RepetitionNotUniqueAdmission

namespace A12Kernel

private def hasStar : ResolvedFieldEntityOperand model → Bool
  | .star _ | .starHaving _ _ | .starredGroup _ | .starredGroupPresence _ => true
  | _ => false

/-- Check a forbidden repetition condition's own admission before its enclosing filter checks.
Only reference scope is retained: no duplicate evaluator is constructed (spec/07 §3 and §6).
The rule's declaration group selects the default branch independently of candidate/captured reads. -/
def elaborateHavingRepetitionAdmission (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels reopenedLevels : List RepeatableLevel)
    (keys : SurfaceHavingEntitySource) (scope : Option SurfaceHavingEntityOperand) :
    Except CorrelationElabError Bool := do
  let reads ← resolveHavingEntityListOperands model declaringGroup candidateLevels outerLevels keys
  let scopeRead ← scope.mapM fun operand => do
    let read ← resolveHavingEntityListOperands model declaringGroup candidateLevels outerLevels
      { first := operand, rest := [] }
    match read with
    | [reference] => pure reference
    | _ => throw .incoherentCore
  checkHavingEntityDuplicates reads
  if let some path := reads.findSome? (fun (_, operand) => operand.categoryPath?) then
    throw (.fieldFill (.categoryNotAllowed path))
  if let some path := reads.findSome? (fun (_, operand) => operand.subtreePath?) then
    throw (.repetitionNotUnique (.groupKey path))
  if reads.any (fun (_, operand) => hasStar operand) then
    throw (.comparisonEntry .noWildcardsAllowed)
  let declarations := reads.flatMap (fun (_, operand) => operand.expansionDeclarations)
  if let some raw := declarations.find? (·.isRawString) then
    throw (.repetitionNotUnique (.rawStringValue raw.path))
  if let some (_, operand) := scopeRead then
    if operand.subtreePath?.isNone then
      throw (.repetitionNotUnique (.scopeIsField operand.entityPath))
    if hasStar operand then throw (.comparisonEntry .noWildcardsAllowed)
  let _ ← checkRepetitionReferenceAdmission model declaringGroup declarations
    (scopeRead.map fun (_, operand) => (operand.entityPath, operand.subtreePath?.isNone))
    |>.mapError .repetitionNotUnique
  pure ((reads ++ scopeRead.toList).any fun (origin, operand) =>
    origin == .inner && operand.bindingScope.any reopenedLevels.contains)

end A12Kernel
