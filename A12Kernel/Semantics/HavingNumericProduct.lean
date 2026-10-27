import A12Kernel.Semantics.HavingEntityList

namespace A12Kernel

/-- The two product references share a checked lowest-star topology, but each retains the
environment selected by its own capture origin (spec/07 §3.8 and §3.2). -/
structure HavingNumericProduct where
  groupPath : GroupPath
  path : StarPath
  left : HavingNumberRef
  right : HavingNumberRef
  deriving Repr, DecidableEq

namespace HavingNumericProduct

def presenceSlots (source : HavingNumericProduct) : List (HavingFieldListSlot HavingPresenceRef) :=
  [source.left, source.right].map fun ref =>
    .extent (.starField source.groupPath source.path) [{ origin := ref.origin, field := ref.field.id }]

def summary (source : HavingNumericProduct) : NumericScaleSummary :=
  .binary .multiply (.field source.left.field.info.scale) (.field source.right.field.info.scale)

private def readPairs (source : HavingNumericProduct) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (omitted : Bool) :
    List (Env × Env) → Rat × NumericFillability → Except Error NumericOperand
  | [], total => pure (.value total.1 (if omitted then .both else total.2))
  | (leftEnv, rightEnv) :: remaining, total => do
      let left ← context.read leftEnv source.left.field.id
      match numericProductCell source.left.field.info.signed (observeCell phase left).asNumberValueListCell with
      | .error cause => pure (.unknown cause)
      | .ok left =>
          let right ← context.read rightEnv source.right.field.id
          match numericProductCell source.right.field.info.signed (observeCell phase right).asNumberValueListCell with
          | .error cause => pure (.unknown cause)
          | .ok right => readPairs source phase context omitted remaining (numericProductStep total left right)

/-- Acquire both authored iterators, pair their rows in order, and stop at the shorter stream.
Each reached pair uses the ordinary staged product/sum fold; a terminal unavailable value
prevents later reads (`RuntimeController.summeVonProdukten`, kernel 30.8.1). -/
def evaluate (source : HavingNumericProduct) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error NumericOperand := do
  let some groups := context.groups | throw (context.groupUnavailable source.groupPath)
  let (left, leftOmitted) ← groups.fieldExtent source.groupPath (frame.envAt source.left.origin)
    source.path.firstStar source.left.field.id
  let (right, rightOmitted) ← groups.fieldExtent source.groupPath (frame.envAt source.right.origin)
    source.path.firstStar source.right.field.id
  readPairs source phase context (leftOmitted || rightOmitted) (left.zip right) (0, .fixed)

end HavingNumericProduct
end A12Kernel
