import A12Kernel.Elaboration.HavingEntityList

namespace A12Kernel

def HavingNumericProduct.wellFormed (source : HavingNumericProduct) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  source.path.firstStar + 1 == source.path.axes.length &&
    source.presenceSlots.all (·.wellFormedForEnvironments model candidateLevels outerLevels) &&
    [source.left, source.right].all (fun ref =>
      (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
        declaration.toNumberField? == some ref.field)

/-- Product shape is not ordinary list shape: repeated use of the same star is legal, while
both Number operands must share the immediate owning group and lowest-star plan (spec/07 §3.8). -/
def elaborateHavingNumericProduct (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) (source : SurfaceHavingEntitySource) :
    Except CorrelationElabError HavingNumericProduct := do
  let operands ← resolveHavingEntityListOperands model declaringGroup candidateLevels outerLevels source
  if let some path := operands.findSome? (·.categoryPath?) then
    throw (.fieldFill (.categoryNotAllowed path))
  let [{ origin := leftOrigin, operand := .star left, form := .stored },
      { origin := rightOrigin, operand := .star right, form := .stored }] := operands
    | throw .numericExpressionUnsupported
  if left.declaration.groupPath != right.declaration.groupPath then throw .numericExpressionUnsupported
  if left.path.firstStar + 1 != left.path.axes.length || left.path != right.path then throw .numericExpressionUnsupported
  let some leftField := left.declaration.toNumberField? | throw .numericExpressionUnsupported
  let some rightField := right.declaration.toNumberField? | throw .numericExpressionUnsupported
  pure {
    groupPath := left.declaration.groupPath, path := left.path
    left := { origin := leftOrigin, field := leftField }
    right := { origin := rightOrigin, field := rightField } }

end A12Kernel
