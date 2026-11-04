import A12Kernel.Reference.Dm.HavingListAdmission
import A12Kernel.Reference.Dm.HavingScalarAdmission
import A12Kernel.Reference.Dm.FilterReferenceInventory

/-! # The gates of `SumOfTerms` around its entity and term reads

The ordered walk in [`HavingAdmission`](HavingAdmission.lean) reads the entity and the term of
`SumOfTerms(G*, t)` itself; the gates that follow those reads are here. The entity must be a
repeatable group whose lowest level carries the star, and the term is a Number operation that draws the
set-expression classes, so it is walked as a filter body is, with the entity's lowest level as the
one it must iterate ([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms)).
-/

namespace A12Kernel.Dm
open HavingListAdmission

/-- The entity gates that follow its read, in the order the entity table lists them: a field is no
group, a group that does not repeat has no rows, and the lowest level must carry the star. A repeatable
level left unstarred below another star, or above the lowest level where the rule does not bind it,
was refused by the read itself. Returns the repeatable levels the entity's rows are iterated at. -/
def sumOfTermsEntityLevels (model : FlatModel) (entity : Reference) (read : RawListRead) :
    Lowering (List RepeatableLevel) := do
  let .inr path := read.entity | refuse "SumOfTerms" KernelStaticDiagnostic.noFieldsAllowed.kernelCode
  if !model.repeatableGroups.any (·.path == path) then
    refuse "SumOfTerms" KernelStaticDiagnostic.groupNotRepeatable.kernelCode
  if !(entity.path.segments.getLast?.any (·.star)) then
    refuse "SumOfTerms" KernelStaticDiagnostic.wildcardAtLowestLevelRequired.kernelCode
  pure (model.repeatableScopeForGroupPath path)

/-- The term's gates once its reads and operations have been admitted: the type it computes, then the
set-expression walk over its references with the entity's lowest level as the only one that counts
as iterated. A term reading no field of that level draws its own class, and a construct a set
expression forbids answers after the walk, as in a filter body. -/
def sumOfTermsTermType (model : FlatModel) (group : GroupPath) (levels : List RepeatableLevel)
    (term : Expr) (tree : AuthoredNumericExpr NumericOperandType) : Lowering NumericOperandType := do
  let type ← rawNumericType model.hasBaseYear tree
  if type.surfaceKind != .number then refuse "SumOfTerms" KernelStaticDiagnostic.noNumber.kernelCode
  let some lowest := levels.getLast? | refuse "SumOfTerms" "entity levels"
  let (references, forbidden) ← filterBodyInventoryAtLevels model group levels [lowest] term (nested := false)
  if let some diagnostic := filterBodyRefusal references forbidden .noIterationForLowestWildcard then
    refuse "SumOfTerms" diagnostic.kernelCode
  pure type

end A12Kernel.Dm
