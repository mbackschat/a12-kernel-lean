import A12Kernel.Document

/-! # Resolved group identity

Group operands retain path segments, authored origin and bound scope across semantic consumers.
Model resolution and operator-specific admission belong to elaboration.
-/

namespace A12Kernel

abbrev GroupPath := List String

inductive GroupReferenceOrigin where
  | path
  | ruleGroup
  deriving Repr, DecidableEq

/-- A resolved group keeps authored origin for stable Transform/Explain consumers instead of erasing
`RuleGroup` into an ordinary path. An ordinary fixed child below repeatable ancestry also retains the
checked evaluation scope; an empty scope is the established scalar case. -/
structure ResolvedGroupReference where
  path : GroupPath
  origin : GroupReferenceOrigin
  boundRepeatableScope : List RepeatableLevel := []
  deriving Repr, DecidableEq


end A12Kernel
