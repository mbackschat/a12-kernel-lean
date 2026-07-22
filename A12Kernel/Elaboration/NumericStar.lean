import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.StarCompleteness

/-! # Checked finite one-level Number stars

This shared boundary validates one authored star against an expanded flat model, retains its positive finite capacity, validates one raw contiguous row prefix, and constructs the ordered checked Number cells plus omitted-tail state consumed by aggregate and first-filled evaluators. Filters, nested stars, partial relevance, messages, protocol, and general `Document` adaptation remain outside.
-/

namespace A12Kernel

/-- Fail-closed errors owned by the shared one-star Number lowering boundary. -/
inductive NumericStarElabError where
  | star (error : SingleGroupElabError)
  | repeatabilityUnavailable (path : GroupPath)
  | invalidRepeatability (path : GroupPath) (repeatability : Nat)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One finite Number star certified against its model declaration. -/
structure CheckedNumericStarSource (model : FlatModel) where
  group : RepeatableGroupDecl
  field : FlatNumberField
  repeatability : Nat
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.repeatableGroups.contains group = true
  fieldOwned : model.admitsSingleGroupNumber group field = true
  repeatabilityOwned : group.repeatability = some repeatability
  repeatabilityValid : 0 < repeatability

/-- Validate the model once, bind the exact starred group and direct-child Number field, and require its declared finite capacity. -/
def elaborateNumericStarSource (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceSingleStarFieldPath) :
    Except NumericStarElabError (CheckedNumericStarSource model) :=
  match hModel : model.validate with
  | .error error => .error (.star (.resolve error))
  | .ok () => do
      let groupReference ← source.groupReference |>.mapError .star
      let groupPath ← groupReference.resolveAgainst declaringGroup |>.mapError .star
      let group ← model.lookupUniqueRepeatablePath groupPath |>.mapError (.star ∘ .resolve)
      let fieldReference : SurfaceFieldPath :=
        { base := .absolute, groups := group.path, field := source.field }
      let (_, field) ←
        model.resolveNumberInGroup declaringGroup group fieldReference |>.mapError .star
      match hRepeatabilityOwned : group.repeatability with
      | none => throw (.repeatabilityUnavailable group.path)
      | some repeatability =>
          if hRepeatability : 0 < repeatability then
            if hGroup : model.repeatableGroups.contains group = true then
              if hField : model.admitsSingleGroupNumber group field = true then
                pure {
                  group
                  field
                  repeatability
                  modelWellFormed := by
                    rw [hModel]
                    rfl
                  groupOwned := hGroup
                  fieldOwned := hField
                  repeatabilityOwned := hRepeatabilityOwned
                  repeatabilityValid := hRepeatability
                }
              else
                throw .incoherentCore
            else
              throw .incoherentCore
          else
            throw (.invalidRepeatability group.path repeatability)

/-- Runtime topology errors at the checked finite one-star boundary. -/
inductive NumericStarContextError where
  | topology (error : SingleGroupContextError)
  | noncontiguousCandidates (candidates : List RowIndex)
  | exceedsRepeatability (actual repeatability : Nat)
  deriving Repr, DecidableEq

namespace CheckedNumericStarSource

private def expectedCandidates (count : Nat) : List RowIndex :=
  (List.range count).map (· + 1)

/-- Require the instantiated rows to be the unique 1-based prefix of the declared finite domain. -/
def validateContext (checked : CheckedNumericStarSource model)
    (raw : RawSingleGroupContext) : Except NumericStarContextError Unit := do
  raw.validate |>.mapError .topology
  if raw.candidates.length > checked.repeatability then
    throw (.exceedsRepeatability raw.candidates.length checked.repeatability)
  if raw.candidates != expectedCandidates raw.candidates.length then
    throw (.noncontiguousCandidates raw.candidates)

/-- Represent the instantiated deepest rows of this one-level checked star. -/
def selectedRows : List RowIndex → ReopenedStarRows
  | [] => .nil
  | row :: rest => .cons row .selectedLeaf (selectedRows rest)

/-- Construct the common resolved side from checked row order, exact cell classification, and the model-owned omitted tail. -/
def resolvedValueSide (checked : CheckedNumericStarSource model)
    (raw : RawSingleGroupContext) : ResolvedValueListSide .number :=
  let context := model.checkSingleGroupContext checked.group raw
  let domain := ReopenedStarDomain.repeatable (some checked.repeatability)
    (selectedRows raw.candidates)
  domain.toResolvedSide
    (raw.candidates.map fun row => checked.field.valueListCell (context.atRow row))

end CheckedNumericStarSource

end A12Kernel
