import A12Kernel.Elaboration.DateRangeInput
import A12Kernel.Elaboration.FieldEntityList

/-! # Checked DateRange overlap operands

This boundary owns operator-specific static admission and later checked-document assembly for DateRange overlap conditions. It reuses the shared entity-list shape and the canonical checked DateRange declaration policy; pure overlap truth and polarity remain in `A12Kernel.Semantics.DateRangeOverlapOperators`.
-/

namespace A12Kernel

/-- Static refusal while certifying the singular DateRange overlap operand list. -/
inductive DateRangesOverlapElabError where
  | shape (error : FieldEntityShapeElabError)
  | sourceNotDateRange (path : List String) (actual : SurfaceScalarKind)
  | unsupportedPolicy (path : List String) (format separator : String)
  | unsupportedReadForm (path : List String) (form : FieldEntityReadForm)
  | groupsNotAllowed (path : GroupPath)
  | having (error : CorrelationElabError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace DateRangesOverlapElabError

def diagnostic? : DateRangesOverlapElabError → Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .groupsNotAllowed _ => some .noGroupsAllowed
  | .sourceNotDateRange _ _ | .unsupportedPolicy _ _ _ |
      .unsupportedReadForm _ _ | .having _ | .incoherentCore => none

end DateRangesOverlapElabError

/-- One certified direct, plain-star, or filter-bearing star DateRange operand. -/
inductive CheckedDateRangesOverlapOperand (model : FlatModel) where
  | field (source : CheckedCanonicalDateRangeField)
  | star (path : CheckedStarFieldPath model)
      (source : CheckedCanonicalDateRangeField)
      (filter : Option CorrelatedHaving)

namespace CheckedDateRangesOverlapOperand

def source : CheckedDateRangesOverlapOperand model →
    CheckedCanonicalDateRangeField
  | .field source | .star _ source _ => source

def hasHaving : CheckedDateRangesOverlapOperand model → Bool
  | .field _ | .star _ _ none => false
  | .star _ _ (some _) => true

end CheckedDateRangesOverlapOperand

/-- A model-checked nonempty `DateRangesOverlap` operand list retaining the shared shape and exact authored filter slots. -/
structure CheckedDateRangesOverlapSource (model : FlatModel) where
  private mk ::
  shape : CheckedFieldEntityShape model
  first : CheckedDateRangesOverlapOperand model
  rest : List (CheckedDateRangesOverlapOperand model)

namespace CheckedDateRangesOverlapSource

def operands (checked : CheckedDateRangesOverlapSource model) :
    List (CheckedDateRangesOverlapOperand model) :=
  checked.first :: checked.rest

def hasHaving (checked : CheckedDateRangesOverlapSource model) : Bool :=
  checked.operands.any CheckedDateRangesOverlapOperand.hasHaving

end CheckedDateRangesOverlapSource

private def certifyDateRangesOverlapField (declaration : FlatFieldDecl) :
    Except DateRangesOverlapElabError CheckedCanonicalDateRangeField :=
  (certifyCanonicalDateRangeField declaration).mapError fun
    | .notDateRange path actual => .sourceNotDateRange path actual.surfaceKind
    | .unsupportedPolicy path format separator =>
        .unsupportedPolicy path format separator
    | .incoherentCore => .incoherentCore

private def certifyDateRangesOverlapOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except DateRangesOverlapElabError
        (CheckedDateRangesOverlapOperand model)
  | .field declaration .stored =>
      .field <$> certifyDateRangesOverlapField declaration
  | .field declaration form =>
      throw (.unsupportedReadForm declaration.path form)
  | .star path => do
      pure (.star path (← certifyDateRangesOverlapField path.declaration) none)
  | .starHaving path authored => do
      let source ← certifyDateRangesOverlapField path.declaration
      let filter ← elaborateStarHavingCore model declaringGroup path authored
        |>.mapError .having
      pure (.star path source (some filter.condition))
  | .group reference => throw (.groupsNotAllowed reference.path)
  | .starredGroup source => throw (.groupsNotAllowed source.group.path)
  | .starredGroupPresence source => throw (.groupsNotAllowed source.groupPath)

private def certifyDateRangesOverlapOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except DateRangesOverlapElabError
        (List (CheckedDateRangesOverlapOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyDateRangesOverlapOperand model declaringGroup operand) ::
        (← certifyDateRangesOverlapOperands model declaringGroup remaining))

/-- Apply the shared shape gates first, then the singular operator's group refusal and exact DateRange policy certification in authored order. -/
def elaborateDateRangesOverlapSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except DateRangesOverlapElabError
      (CheckedDateRangesOverlapSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  let first ← certifyDateRangesOverlapOperand model declaringGroup shape.first
  let rest ← certifyDateRangesOverlapOperands model declaringGroup shape.rest
  pure { shape, first, rest }

end A12Kernel
