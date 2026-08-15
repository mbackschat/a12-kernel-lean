import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Checked String `FieldValuesNotUnique`

This consumer applies the common checked token entity list to `FieldValuesNotUnique`, specializing the shared whole-list gate to one String or Enumeration category. Real-kernel authoring admits two Strings or two stored Enumerations, refuses either mix and any other admissible category with `MVK_VARYING_TYPES_NOT_ALLOWED`, and reports the preempting `MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED` for BOOLEAN or CONFIRM anywhere in the list. This is stricter than `NumberOfDifferentValues`, which admits the String/Enumeration mix. Slot resolution, authored order, repeated-direct rejection, and the multiple-slots-or-one-star rule stay in the shared entity-list owners; membership stays with the shared distinct scan, which compares canonical tokens exactly and therefore does not case-fold.
-/

namespace A12Kernel

abbrev SurfaceTokenValuesNotUniqueSource := SurfaceTokenEntitySource

inductive TokenValuesNotUniqueElabError where
  | source (cause : TokenEntityElabError)
  | inadmissibleKind (path : List String) (actual : SurfaceScalarKind)
  | mixedCategories (path : List String) (actual : SurfaceScalarKind)
  deriving Repr, DecidableEq

namespace CheckedTokenEntityOperand

/-- The operand's declared surface kind. Only the uniqueness predicate constrains this; the distinct count deliberately admits a comparable mix, so this stays local to that consumer's need. -/
def declaredKind : CheckedTokenEntityOperand model → SurfaceScalarKind
  | .field source => source.declaration.policy.kind.surfaceKind
  | .star source => source.source.declaration.policy.kind.surfaceKind

end CheckedTokenEntityOperand

/-- One checked token `FieldValuesNotUnique` operand list, certified to carry a single declared kind. -/
structure CheckedTokenValuesNotUniqueSource (model : FlatModel) where
  private mk ::
  source : CheckedTokenEntitySource model
  oneDeclaredKind :
    ∀ operand ∈ source.rest,
      operand.declaredKind = source.first.declaredKind

/-- Admit one token operand list in Kernel order: common shape, whole-list kind refusal, one String
    or Enumeration category, then the existing token certificate. -/
def elaborateTokenValuesNotUniqueSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceTokenValuesNotUniqueSource) :
    Except TokenValuesNotUniqueElabError
      (CheckedTokenValuesNotUniqueSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError fun error => .source (.shape error)
  match firstFieldListKindRefusal? shape.operands with
  | some refusal => throw (.inadmissibleKind refusal.path refusal.actual)
  | none => pure ()
  match firstFieldListDeclaration? shape.operands with
  | none => pure ()
  | some declaration =>
      match declaration.policy.kind.surfaceKind.fieldListAdmission with
      | .refusedByKind =>
          throw (.inadmissibleKind declaration.path
            declaration.policy.kind.surfaceKind)
      | .category expected =>
          match firstFieldListCategoryMismatch? expected shape.operands with
          | some mismatch => throw (.mixedCategories mismatch.path mismatch.actual)
          | none => pure ()
  let source ← certifyTokenEntityShape model declaringGroup shape |>.mapError .source
  if hKinds : ∀ operand ∈ source.rest,
      operand.declaredKind = source.first.declaredKind then
    pure { source, oneDeclaredKind := hKinds }
  else
    throw (.source .incoherentCore)

namespace TokenValuesNotUniqueElabError

/-- Project this overload's own two kind classes, and delegate every shape refusal to the shared checker's projection: the star, arity, and duplicate gates are that checker's and do not vary by carrier. -/
def diagnostic? : TokenValuesNotUniqueElabError → Option KernelStaticDiagnostic
  | .source (.shape error) => error.diagnostic?
  | .inadmissibleKind _ _ => some .onlyStringEnumNumberDateAllowed
  | .mixedCategories _ _ => some .varyingTypesNotAllowed
  | _ => none

end TokenValuesNotUniqueElabError

namespace CheckedTokenValuesNotUniqueSource

/-- Evaluate the uniqueness predicate from one immutable model-certified checked document. Slots resolve in authored order and every reached cell reaches the scan, because this operator skips a formally unavailable cell instead of suppressing on it. The result carries firing polarity because a reached filter retypes the message. -/
def evaluateCheckedDocumentValuesNotUnique
    (checked : CheckedTokenValuesNotUniqueSource model)
    (document : CheckedDocument model) (outer : Env) : Except CheckedAddressingError Verdict := do
  let tagged ← collectTaggedValueListCells
    (fun operand => do
      let resolved ← operand.resolveCheckedValidationOperand document outer
      pure (resolved.valueListSideAt .validation))
    checked.source.operands
  pure (evalValuesNotUniqueVerdict tagged)

end CheckedTokenValuesNotUniqueSource

end A12Kernel
