import A12Kernel.Elaboration.TokenDistinctCount

/-! # Checked String `FieldValuesNotUnique`

This consumer applies the common checked token entity list to `FieldValuesNotUnique`, adding the one admission rule that distinguishes this operator from the distinct count it sits beside: every operand must share **one declared kind**. Real-kernel authoring admits two String fields and refuses String beside stored Enumeration with `MVK_VARYING_TYPES_NOT_ALLOWED`, even though `NumberOfDifferentValues` explicitly admits that mix. Slot admission, authored order, repeated-direct rejection, and the multiple-slots-or-one-star rule stay in `TokenEntityList`; the membership boundary stays with the shared distinct scan, which compares canonical tokens exactly and therefore does not case-fold.
-/

namespace A12Kernel

abbrev SurfaceTokenValuesNotUniqueSource := SurfaceTokenEntitySource

inductive TokenValuesNotUniqueElabError where
  | source (cause : TokenEntityElabError)
  | mixedDeclaredKinds
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

/-- Admit one token operand list and then reject a mixed-kind list, which the shared entity-list contract permits for comparability but this operator refuses. -/
def elaborateTokenValuesNotUniqueSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceTokenValuesNotUniqueSource) :
    Except TokenValuesNotUniqueElabError
      (CheckedTokenValuesNotUniqueSource model) := do
  let source ←
    elaborateTokenEntitySource model declaringGroup authored |>.mapError .source
  if hKinds : ∀ operand ∈ source.rest,
      operand.declaredKind = source.first.declaredKind then
    pure { source, oneDeclaredKind := hKinds }
  else
    throw .mixedDeclaredKinds

namespace CheckedTokenValuesNotUniqueSource

/-- Evaluate the uniqueness predicate from one immutable model-certified checked document. Slots resolve in authored order and the first formally unavailable reached cell stops the scan. -/
def evaluateCheckedDocumentValuesNotUnique
    (checked : CheckedTokenValuesNotUniqueSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError K := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueListSide .token) (terminal := K)
      (fun operand => do
        let resolved ← operand.resolveCheckedValidationOperand document outer
        pure (.inl (resolved.valueListSideAt .validation)))
      (fun _cause => K.unknown)
      (fun accumulated _ side => accumulated.append side)
      checked.source.operands ResolvedValueListSide.empty with
  | .inl side => pure (evalValuesNotUnique side.cells)
  | .inr verdict => pure verdict

end CheckedTokenValuesNotUniqueSource

end A12Kernel
