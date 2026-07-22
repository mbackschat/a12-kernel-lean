import A12Kernel.Elaboration.ValidationCondition

/-! # Shared resolved validation-condition locks -/

namespace A12Kernel.Conformance.ValidationCondition

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

private def u : FlatNumberField := { id := 1, info := unsigned }
private def v : FlatNumberField := { id := 2, info := unsigned }

private def model : FlatModel :=
  { fields := [
      { id := u.id, groupPath := ["Order"], name := "U",
        policy := { kind := .number unsigned } },
      { id := v.id, groupPath := ["Order"], name := "V",
        policy := { kind := .number unsigned } }] }

private def fieldPath (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def numericSurface : SurfaceNumericComparison :=
  { op := .ordinary .greater
    left := .atom (.field (fieldPath "V"))
    right := .literal { value := 0, authoredScale := 0 } }

private def condition? : Option ValidationCondition := do
  let checked ← (elaborateNumericComparison model ["Order"] numericSurface).toOption
  pure (.and
    (ValidationCondition.flat (.fieldFilled (.number u)))
    (ValidationCondition.numeric checked.core))

private def raw (uCell vCell : RawCell) : RawFlatContext where
  read id := if id == u.id then uCell else if id == v.id then vCell else .empty

private def verdictOf (uCell vCell : RawCell)
    (relevant : FieldId → Bool := fun _ => true) : Option Verdict := do
  let condition ← condition?
  pure (condition.evalSelected (model.checkContext (raw uCell vCell)) relevant)

/- A mixed tree combines an ordinary presence leaf with a checked numeric-expression leaf through the same connective semantics. -/
example : verdictOf (.parsed (.num 1)) (.parsed (.num 2)) =
    some (.fired .value) := by
  native_decide

/- Flat-left false short-circuits the numeric leaf, while a reached out-of-set numeric reference remains UNKNOWN. -/
example :
    verdictOf .presentEmpty (.rejected .malformed) (fun id => id == u.id) =
        some .notFired ∧
    verdictOf (.parsed (.num 1)) (.parsed (.num 2)) (fun id => id == u.id) =
        some .unknown := by
  native_decide

/- One reference traversal sees both leaf families. -/
example : condition?.map (fun condition =>
    condition.referencesField u.id && condition.referencesField v.id) = some true := by
  native_decide

end A12Kernel.Conformance.ValidationCondition
