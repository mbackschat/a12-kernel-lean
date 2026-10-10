import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Semantics.StarAddressing

namespace A12Kernel

/-- Resolve one validated field or group scope to the shared structural axes. A checked model makes failure unreachable; retaining `Option` keeps malformed internal callers explicit. -/
def FlatModel.repeatableAxesForScope? (model : FlatModel) :
    List RepeatableLevel → Option (List StarAxis)
  | [] => some []
  | level :: levels => do
      let group ← model.repeatableGroupAtLevel? level
      let remaining ← model.repeatableAxesForScope? levels
      pure ({ level, repeatability := group.repeatability } :: remaining)

/-- Apply the shared over-capacity decision to one exact model scope and coordinate path. Address depth and zero-coordinate checks remain owned by placement validation. -/
def FlatModel.addressOverLimit? (model : FlatModel)
    (scope : List RepeatableLevel) (path : List Nat) : Option Bool := do
  let axes ← model.repeatableAxesForScope? scope
  pure (StarAxes.environmentOverLimit axes (scope.zip path))

end A12Kernel
