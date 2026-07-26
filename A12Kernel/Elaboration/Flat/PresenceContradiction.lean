import A12Kernel.Elaboration.Flat.Condition

/-! # Exact flat presence-contradiction analysis -/

namespace A12Kernel

/-- The two authored orders of the exact same-field presence contradiction. -/
inductive FlatPresenceContradictionOrder where
  | filledThenNotFilled
  | notFilledThenFilled
  deriving Repr, DecidableEq

/-- Reconstruct the exact condition certified by one presence-contradiction order. -/
def FlatPresenceContradictionOrder.condition
    (order : FlatPresenceContradictionOrder)
    (field : FlatField) : FlatCondition :=
  match order with
  | .filledThenNotFilled =>
      .and (FlatCondition.fieldFilled field) (FlatCondition.fieldNotFilled field)
  | .notFilledThenFilled =>
      .and (FlatCondition.fieldNotFilled field) (FlatCondition.fieldFilled field)

/-- A proof-bearing witness that a flat condition has one exact dead presence shape. -/
structure FlatPresenceContradictionWitness (condition : FlatCondition) where
  field : FlatField
  order : FlatPresenceContradictionOrder
  exactShape : condition = order.condition field

private def detectPresenceContradiction (condition : FlatCondition) :
    Option (FlatPresenceContradictionWitness condition) :=
  match condition with
  | .and (.leaf (.fieldFilled left)) (.leaf (.fieldNotFilled right)) =>
      if same : left = right then
        some {
          field := left
          order := .filledThenNotFilled
          exactShape := by subst right; rfl }
      else
        none
  | .and (.leaf (.fieldNotFilled left)) (.leaf (.fieldFilled right)) =>
      if same : left = right then
        some {
          field := left
          order := .notFilledThenFilled
          exactShape := by subst right; rfl }
      else
        none
  | _ => none

/-- Detect only the exact root-level same-field conjunction in an already-checked flat condition. The dependent result carries its own shape certificate. -/
def CheckedFlatCondition.presenceContradiction?
    (checked : CheckedFlatCondition model) :
    Option (FlatPresenceContradictionWitness checked.core) :=
  detectPresenceContradiction checked.core

end A12Kernel
