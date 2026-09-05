import A12Kernel.Elaboration.TemporalValuesNotUnique

/-! # Checked temporal `NumberOfDifferentValues`

The temporal overload of the distinct count, and the operator that sits closest to
`FieldValuesNotUnique` while gating differently. Slot certification, authored order, and the
shared shape rules are that neighbour's and are reused unchanged; what differs is the one thing
this module owns.

**Admission is the operand list's shared component set, not its shared declared format.** Two DATE
fields spelled `yyyy-MM-dd` and `dd.MM.yyyy` name the same components and are **admitted** here,
while the neighbouring uniqueness operator refuses that exact pair; a differing set such as
`yyyy-MM-dd` beside `yyyy-MM` is refused `MVK_DATEFORMATS_NOT_COMPATIBLE` naming both formats
([checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-distinct-count-component-set-and-locus)).
So the two operators genuinely differ on one field pair and neither gate may be read off the other.

The component set is taken from the **declaration**, which is equivalent to reading it off the
declared format on every model this project admits: the stored-text classifiers already refuse a
declaration whose format and component set contradict each other, and whether the Kernel accepts
such a declaration at all is unmeasured and owned by SG21. Stated as a total function either way, so
no reachability question gates the clause.

**Scope: direct field and starred operands.** A group operand is declined rather than admitted,
because the reusable group certificate carries its neighbour's format-equality gate and no retained
row measures a group expansion at this operator. The decline claims no Kernel class.
-/

namespace A12Kernel

/-- The component set a certified temporal operand's declaration names. Total: a slot that reached
    certification carries a temporal kind, and the non-temporal arm cannot occur. -/
def CheckedTemporalUniquenessField.components
    (checked : CheckedTemporalUniquenessField) : TemporalComponents :=
  match checked.declaration.policy.kind with
  | .temporal _ components => components
  | _ =>
      { year := false, month := false, day := false
        hour := false, minute := false, second := false }

/-- The component set one slot contributes to the list's gate. -/
def CheckedTemporalUniquenessOperand.components :
    CheckedTemporalUniquenessOperand model → TemporalComponents
  | .field source | .star _ source _ => source.components
  | .group source => source.first.components

inductive TemporalDistinctCountElabError where
  /-- A slot refusal from the shared temporal certifier. Wrapped rather than restated because slot
      certification is identical across the two operators; the **codes** are not, so the projection
      below re-maps each arm instead of delegating. -/
  | slot (error : TemporalValuesNotUniqueElabError)
  /-- **This operator's own gate.** An operand whose component set differs from the list's, carrying
      both declared formats because the Kernel's message names them rather than the sets. -/
  | mixedComponentSets (path : List String) (found expected : String)
  /-- A group slot. Declined rather than refused: the shared group certificate gates on format
      equality, which is the neighbouring operator's rule, and no row measures a group expansion
      here. Claims no Kernel class. -/
  | groupOperandUnsupported (path : List String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Find the first operand whose component set differs from the list's, reporting its path, its own
    declared format, and the list's. Public because the certificate states its gate in terms of it. -/
def firstMismatchedTemporalComponents?
    (expectedComponents : TemporalComponents) (expectedFormat : String) :
    List (CheckedTemporalUniquenessOperand model) →
      Option (List String × String × String)
  | [] => none
  | operand :: remaining =>
      if operand.components == expectedComponents then
        firstMismatchedTemporalComponents? expectedComponents expectedFormat remaining
      else
        some (operand.path, operand.format, expectedFormat)

/-- One checked temporal distinct-count operand list, certified to share a single component set.
    Deliberately **not** certified to share a format: that is the neighbour's gate and would refuse
    a pair the Kernel admits. -/
structure CheckedTemporalDistinctCountSource (model : FlatModel) where
  private mk ::
  shape : CheckedFieldEntityShape model
  first : CheckedTemporalUniquenessOperand model
  rest : List (CheckedTemporalUniquenessOperand model)
  oneComponentSet :
    firstMismatchedTemporalComponents? first.components first.format rest = none

namespace CheckedTemporalDistinctCountSource

def operands (checked : CheckedTemporalDistinctCountSource model) :
    List (CheckedTemporalUniquenessOperand model) :=
  checked.first :: checked.rest

/-- The list's shared component set, which every operand carries by construction. -/
def components (checked : CheckedTemporalDistinctCountSource model) :
    TemporalComponents :=
  checked.first.components

end CheckedTemporalDistinctCountSource

/-- The group path of a slot this operator declines, or `none` for a slot it certifies. -/
private def groupSlotPath? :
    ResolvedFieldEntityOperand model → Option (List String)
  | .group reference => some reference.path
  | .starredGroup source => some source.group.path
  | .starredGroupPresence source => some source.groupPath
  | .field .. | .star _ | .starHaving _ _ => none

/-- Certify one authored operand list for the temporal distinct count.

    Slot certification is the shared one; the list gate is this operator's own. A **group** slot is
    declined here rather than certified, because the shared group certificate carries the
    neighbouring operator's format-equality gate and no retained row measures a group expansion at
    this operator — the decline claims no Kernel class. -/
def elaborateTemporalDistinctCountSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except TemporalDistinctCountElabError
      (CheckedTemporalDistinctCountSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError fun error => .slot (.shape error)
  match firstKindGateRefusal? shape.operands with
  | some refusal => throw (.slot refusal)
  | none => pure ()
  match (shape.first :: shape.rest).findSome? groupSlotPath? with
  | some path => throw (.groupOperandUnsupported path)
  | none => pure ()
  let first ← (certifyTemporalUniquenessOperand model declaringGroup shape.first).mapError .slot
  let rest ← (certifyTemporalUniquenessOperands model declaringGroup shape.rest).mapError .slot
  match hComponents :
      firstMismatchedTemporalComponents? first.components first.format rest with
  | some (path, found, expected) =>
      throw (.mixedComponentSets path found expected)
  | none => pure { shape, first, rest, oneComponentSet := hComponents }

namespace TemporalDistinctCountElabError

/-- Project this operator's own gate and delegate the shared shape classes. The component-set
    refusal is `MVK_DATEFORMATS_NOT_COMPATIBLE`, measured naming both formats; the declined group
    slot claims nothing. -/
def diagnostic? : TemporalDistinctCountElabError → Option KernelStaticDiagnostic
  | .mixedComponentSets _ _ _ => some .dateFormatsNotCompatible
  -- Re-mapped, never delegated: the shared certifier's own projection carries the neighbour's
  -- codes, and the two operators' kind-domain classes differ by one token —
  -- `MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED` here against the `CMP_`-less form there.
  | .slot (.inadmissibleKind _ _) => some .onlyStringEnumNumberCmpDateAllowed
  | .slot (.mixedCategories _ _) => some .dateAndNonDate
  | .slot (.shape error) => error.diagnostic?
  | .slot _ => none
  | .groupOperandUnsupported _ | .incoherentCore => none

end TemporalDistinctCountElabError

end A12Kernel
