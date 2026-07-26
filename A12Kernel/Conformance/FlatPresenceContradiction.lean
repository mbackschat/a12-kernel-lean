import A12Kernel.Elaboration.Flat.PresenceContradiction
import A12Kernel.Conformance.Elaboration.Support

/-! # Solver-free flat presence-contradiction locks -/

namespace A12Kernel.Conformance.FlatPresenceContradiction

open A12Kernel
open A12Kernel.Conformance.Elaboration.Support

private def quantity : SurfaceFieldPath :=
  absolute ["Order"] "Quantity"

private def express : SurfaceFieldPath :=
  absolute ["Order"] "ExpressShipping"

private def analyzed (condition : SurfaceCondition) :
    Option (FlatField × FlatPresenceContradictionOrder) :=
  match elaborate model ["Order"] condition with
  | .ok checked =>
      checked.presenceContradiction?.map fun witness =>
        (witness.field, witness.order)
  | .error _ => none

example :
    analyzed (.and (.fieldFilled quantity) (.fieldNotFilled quantity)) =
      some (.number { id := 0, info := numberInfo },
        .filledThenNotFilled) := by
  native_decide

example :
    analyzed (.and (.fieldNotFilled quantity) (.fieldFilled quantity)) =
      some (.number { id := 0, info := numberInfo },
        .notFilledThenFilled) := by
  native_decide

/- The exact `Or` counterpart is not the dead-condition shape. -/
example :
    analyzed (.or (.fieldFilled quantity) (.fieldNotFilled quantity)) = none := by
  native_decide

/- Opposite presence predicates on different fields can hold together. -/
example :
    analyzed (.and (.fieldFilled quantity) (.fieldNotFilled express)) = none := by
  native_decide

private def checked (kind : FieldKind) (raw : RawCell) : CheckedCell :=
  formalCheck { kind } raw

private def invalidQuantityContext : FlatContext where
  read fieldId :=
    if fieldId = 0 then checked (.number numberInfo) (.rejected .malformed)
    else checked .boolean .empty

private def differentFieldsContext : FlatContext where
  read fieldId :=
    if fieldId = 0 then checked (.number numberInfo) (.parsed (.num 1))
    else checked .boolean .empty

private def quantityField : FlatField :=
  .number { id := 0, info := numberInfo }

private def expressField : FlatField :=
  .boolean { id := 1 }

private def quantityPresenceEither : FlatCondition :=
  .or (FlatCondition.fieldFilled quantityField)
    (FlatCondition.fieldNotFilled quantityField)

private def differentFieldPresenceBoth : FlatCondition :=
  .and (FlatCondition.fieldFilled quantityField)
    (FlatCondition.fieldNotFilled expressField)

/- `FieldFilled(f) Or FieldNotFilled(f)` is not a tautology under formal UNKNOWN. -/
example :
    quantityPresenceEither.evalSelected invalidQuantityContext = .unknown := by
  native_decide

/- Partial nonrelevance supplies the same non-tautology boundary. -/
example :
    quantityPresenceEither.evalSelected differentFieldsContext
      (fun _ => false) = .unknown := by
  native_decide

/- The different-field conjunction is genuinely reachable. -/
example :
    differentFieldPresenceBoth.evalSelected differentFieldsContext =
      .fired .omission := by
  native_decide

end A12Kernel.Conformance.FlatPresenceContradiction
