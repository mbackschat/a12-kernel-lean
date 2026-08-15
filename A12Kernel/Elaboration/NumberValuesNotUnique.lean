import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Checked Number `FieldValuesNotUnique`

This consumer applies the common checked Number entity list to `FieldValuesNotUnique`. It specializes the shared whole-list kind/category gate to Number before entering the existing Number certificate, projects the measured arity, kind, and mixing diagnostics, and owns the uniqueness verdict. Slot resolution, authored order, repeated-direct-field rejection, the multiple-slots-or-one-star rule, and Number-valued certification stay in the shared entity-list owners, while membership stays with the shared distinct scan.

Real-kernel authoring admits the plain field list over two or three Number fields of differing declared scales, the starred single-field form, and a mixed direct-plus-starred list. A single direct operand reports `MVK_PARAMSIZE_INVALIDN`, another admissible category reports `MVK_VARYING_TYPES_NOT_ALLOWED`, and BOOLEAN or CONFIRM anywhere in the list reports the preempting `MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED`. The String/stored-Enumeration and date-like overloads remain separate checked consumers.
-/

namespace A12Kernel

abbrev SurfaceNumberValuesNotUniqueOperand := SurfaceNumberEntityOperand
abbrev SurfaceNumberValuesNotUniqueSource := SurfaceNumberEntitySource
abbrev CheckedNumberValuesNotUniqueSource := CheckedNumberEntitySource

inductive NumberValuesNotUniqueElabError where
  | shape (error : FieldEntityShapeElabError)
  | inadmissibleKind (path : List String) (actual : SurfaceScalarKind)
  | mixedCategories (path : List String) (actual : SurfaceScalarKind)
  | source (error : NumberEntityElabError)
  deriving Repr, DecidableEq

/-- Admit one Number `FieldValuesNotUnique` list in Kernel order: common shape, whole-list kind
    refusal, Number-category homogeneity, then the existing Number certificate. -/
def elaborateNumberValuesNotUniqueSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumberValuesNotUniqueSource) :
    Except NumberValuesNotUniqueElabError
      (CheckedNumberValuesNotUniqueSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  match firstFieldListKindRefusal? shape.operands with
  | some refusal => throw (.inadmissibleKind refusal.path refusal.actual)
  | none => pure ()
  match firstFieldListCategoryMismatch? .number shape.operands with
  | some mismatch => throw (.mixedCategories mismatch.path mismatch.actual)
  | none => pure ()
  certifyNumberEntityShape model declaringGroup shape |>.mapError .source

namespace NumberValuesNotUniqueElabError

/-- Project this overload's own two kind classes, and delegate every shape refusal to the shared checker's projection: the star, arity, and duplicate gates are that checker's and do not vary by carrier. -/
def diagnostic? : NumberValuesNotUniqueElabError → Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .inadmissibleKind _ _ => some .onlyStringEnumNumberDateAllowed
  | .mixedCategories _ _ => some .varyingTypesNotAllowed
  | .source _ => none

end NumberValuesNotUniqueElabError

namespace CheckedNumberValuesNotUniqueSource

/-- Evaluate the uniqueness predicate from one immutable model-certified checked document. Slots resolve in authored order and every reached cell reaches the scan, because this operator skips a formally unavailable cell instead of suppressing on it. The result carries firing polarity because a reached filter retypes the message.

Deliberately **not** `resolvedCheckedDocumentValidationAggregateSide`: that resolver converts the first unavailable cell into an operand-level unknown terminal, which is what the aggregates beside this operator need and what this one must not do. -/
def evaluateCheckedDocumentValuesNotUnique
    (checked : CheckedNumberEntitySource model)
    (document : CheckedDocument model) (outer : Env) : Except CheckedAddressingError Verdict := do
  let tagged ← collectTaggedValueListCells
    (fun operand => do
      let resolved ← operand.resolveCheckedValidationOperand document outer
      pure (resolved.valueListSideAt .validation))
    checked.operands
  pure (evalValuesNotUniqueVerdict tagged)

end CheckedNumberValuesNotUniqueSource

end A12Kernel
