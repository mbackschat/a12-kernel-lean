import A12Kernel.Elaboration.NumberValuesNotUnique

/-! # `FieldValuesNotUnique` conformance locks over the Number overload

The cross-scale half of the clause's typed equality is inherited rather than exhibited here: a declaration-owned reader has already produced one exact rational per present cell, so a scale-0 `5` and a scale-2 `5.00` arrive as the same atom and membership then uses the ordinary scale-19 comparison boundary.
-/

namespace A12Kernel

private def numberSide (cells : List (ValueListCell .number)) :
    ResolvedValueListSide .number :=
  { cells, hasUninstantiatedTail := false, hasHaving := false }

/- Two equal present values fire the error condition; distinct values do not. -/
example :
    evalValuesNotUnique (numberSide [.present 5, .present 5]).cells = .tru ∧
    evalValuesNotUnique (numberSide [.present 5, .present 6]).cells = .fls := by
  native_decide

/- Empty cells are skipped rather than compared, so two empties are not a duplicate and one empty beside a value is not either. -/
example :
    evalValuesNotUnique (numberSide [.empty, .empty]).cells = .fls ∧
    evalValuesNotUnique (numberSide [.present 5, .empty]).cells = .fls ∧
    evalValuesNotUnique (numberSide [.empty, .present 5, .empty]).cells = .fls := by
  native_decide

/- A duplicate among three operands still fires, and equality is by value rather than by position. -/
example :
    evalValuesNotUnique
      (numberSide [.present 5, .present 6, .present 5]).cells = .tru ∧
    evalValuesNotUnique
      (numberSide [.present 5, .present 6, .present 7]).cells = .fls := by
  native_decide

/- A formally unavailable operand suppresses, and it does so whether or not a duplicate is present. The precedence over an already-seen duplicate is internal: the measured route only exercised suppression without a duplicate. -/
example :
    evalValuesNotUnique
      (numberSide [.present 5, .unknown .malformed, .present 5]).cells
      = .unknown ∧
    evalValuesNotUnique
      (numberSide [.present 5, .present 5, .unknown .declaredConstraint]).cells
      = .unknown ∧
    evalValuesNotUnique
      (numberSide [.unknown .declaredConstraint, .present 5]).cells
      = .unknown := by
  native_decide

/- A single present value can never be a duplicate, and an empty list is vacuously unique. -/
example :
    evalValuesNotUnique (numberSide [.present 5]).cells = .fls ∧
    evalValuesNotUnique (numberSide []).cells = .fls := by
  native_decide

end A12Kernel
