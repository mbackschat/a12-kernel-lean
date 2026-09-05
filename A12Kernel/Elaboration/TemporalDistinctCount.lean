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

**A group operand is admitted, and its expansion is gated by this operator's rule.** The group's
own certificate is therefore this module's rather than the neighbour's: a group carrying one
component set in two spellings is admitted here and refused there, on the identical group
([checkpoint](../../docs/SOURCES.md#src-temporal-group-operand-follows-its-own-operator)). Two
completed users whose gates genuinely differ is the case the reuse rule excludes, so the certificate
is duplicated deliberately. A fixed group beneath an unstarred repeatable ancestor is refused by the
ordinary binding rule, which is the shared shape checker's business and not this gate's.
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

/-- The component set one shared slot contributes to the list's gate. -/
def CheckedTemporalUniquenessOperand.components :
    CheckedTemporalUniquenessOperand model → TemporalComponents
  | .field source | .star _ source _ => source.components
  | .group source => source.first.components

/-- Find the first expanded declaration whose component set differs from the group's own, reporting
    its path and its declared format. The group's **internal** agreement obligation, which is this
    operator's gate and not the neighbour's. -/
def firstMismatchedTemporalFieldComponents?
    (expected : TemporalComponents) :
    List CheckedTemporalUniquenessField → Option (List String × String)
  | [] => none
  | field :: remaining =>
      if field.components == expected then
        firstMismatchedTemporalFieldComponents? expected remaining
      else
        some (field.path, field.format)

/-- One authored group slot certified for **this** operator: a nonempty, wholly temporal expansion
    agreeing on one component set.

    Deliberately not the neighbour's `CheckedTemporalUniquenessGroup`, whose `oneDeclaredFormat`
    obligation is the uniqueness carrier's gate. That certificate refuses a group carrying one
    component set in two spellings, and the Kernel **admits** exactly that group here while refusing
    it there ([checkpoint](../../docs/SOURCES.md#src-temporal-group-operand-follows-its-own-operator)).
    Two completed users whose gates genuinely differ is the case the reuse rule excludes, so the
    certificate is duplicated on purpose rather than parameterized. -/
structure CheckedTemporalDistinctCountGroup (model : FlatModel) where
  private mk ::
  source : CheckedEntityGroupSource model
  first : CheckedTemporalUniquenessField
  rest : List CheckedTemporalUniquenessField
  expansionOwned :
    (model.groupSubtreeFields source.groupPath).filterMap
      FlatFieldDecl.toTemporalUniquenessField? = first :: rest
  expansionAllTemporal :
    (model.groupSubtreeFields source.groupPath).all
      (fun declaration => declaration.toTemporalUniquenessField?.isSome) = true
  oneComponentSet :
    firstMismatchedTemporalFieldComponents? first.components rest = none

namespace CheckedTemporalDistinctCountGroup

def groupPath (group : CheckedTemporalDistinctCountGroup model) : GroupPath :=
  group.source.groupPath

def declarations (group : CheckedTemporalDistinctCountGroup model) :
    List FlatFieldDecl :=
  (group.first :: group.rest).map (·.declaration)

def components (group : CheckedTemporalDistinctCountGroup model) :
    TemporalComponents :=
  group.first.components

def format (group : CheckedTemporalDistinctCountGroup model) : String :=
  group.first.format

end CheckedTemporalDistinctCountGroup

/-- One certified slot of this operator's list. The scalar forms reuse the shared certifier
    unchanged; only the group arm is this operator's own, for the reason its certificate states. -/
inductive CheckedTemporalDistinctCountOperand (model : FlatModel) where
  | slot (operand : CheckedTemporalUniquenessOperand model)
  | group (source : CheckedTemporalDistinctCountGroup model)

namespace CheckedTemporalDistinctCountOperand

def components : CheckedTemporalDistinctCountOperand model → TemporalComponents
  | .slot operand => operand.components
  | .group source => source.components

def format : CheckedTemporalDistinctCountOperand model → String
  | .slot operand => operand.format
  | .group source => source.format

def path : CheckedTemporalDistinctCountOperand model → List String
  | .slot operand => operand.path
  | .group source => source.groupPath

end CheckedTemporalDistinctCountOperand

inductive TemporalDistinctCountElabError where
  /-- A slot refusal from the shared temporal certifier. Wrapped rather than restated because slot
      certification is identical across the two operators; the **codes** are not, so the projection
      below re-maps each arm instead of delegating. -/
  | slot (error : TemporalValuesNotUniqueElabError)
  /-- **This operator's own gate.** An operand whose component set differs from the list's, carrying
      both declared formats because the Kernel's message names them rather than the sets. -/
  | mixedComponentSets (path : List String) (found expected : String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Find the first operand whose component set differs from the list's, reporting its path, its own
    declared format, and the list's. Public because the certificate states its gate in terms of it. -/
def firstMismatchedTemporalComponents?
    (expectedComponents : TemporalComponents) (expectedFormat : String) :
    List (CheckedTemporalDistinctCountOperand model) →
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
  first : CheckedTemporalDistinctCountOperand model
  rest : List (CheckedTemporalDistinctCountOperand model)
  oneComponentSet :
    firstMismatchedTemporalComponents? first.components first.format rest = none

namespace CheckedTemporalDistinctCountSource

def operands (checked : CheckedTemporalDistinctCountSource model) :
    List (CheckedTemporalDistinctCountOperand model) :=
  checked.first :: checked.rest

/-- The list's shared component set, which every operand carries by construction. -/
def components (checked : CheckedTemporalDistinctCountSource model) :
    TemporalComponents :=
  checked.first.components

end CheckedTemporalDistinctCountSource

/-- The group source a slot names, or `none` for a scalar slot. Every group form resolves to the
    shared `CheckedEntityGroupSource`, so all three are certified by one path here. -/
private def groupSlotSource? :
    ResolvedFieldEntityOperand model → Option (CheckedEntityGroupSource model)
  | .group reference => some (.fixed reference)
  | .starredGroup source => some (.starred source)
  | .starredGroupPresence source => some (.starredPresence source)
  | .field .. | .star _ | .starHaving _ _ => none

/-- Certify one group slot against **this** operator's component-set gate. -/
private def certifyDistinctCountGroup (model : FlatModel)
    (source : CheckedEntityGroupSource model) :
    Except TemporalDistinctCountElabError
      (CheckedTemporalDistinctCountOperand model) :=
  let declarations := model.groupSubtreeFields source.groupPath
  if hAll : declarations.all
      (fun declaration => declaration.toTemporalUniquenessField?.isSome) = true then
    match hExpansion : declarations.filterMap
        FlatFieldDecl.toTemporalUniquenessField? with
    | [] => throw (.slot (.groupExpansionEmpty source.groupPath))
    | first :: rest =>
        match hComponents :
            firstMismatchedTemporalFieldComponents? first.components rest with
        | some (path, found) =>
            throw (.mixedComponentSets path found first.format)
        | none =>
            pure (.group {
              source
              first
              rest
              expansionOwned := hExpansion
              expansionAllTemporal := hAll
              oneComponentSet := hComponents })
  else
    -- A non-temporal declaration anywhere in the expansion. The offending declaration is found and
    -- re-certified so the refusal names **its** kind and path rather than a fabricated one; the
    -- shared certifier reports the same way, and disagreeing here would give one group two
    -- different refusals depending on which operator read it.
    match declarations.find? fun declaration =>
        declaration.toTemporalUniquenessField?.isNone with
    | some declaration =>
        match certifyTemporalUniquenessField declaration with
        | .error error => throw (.slot error)
        | .ok _ => throw .incoherentCore
    | none => throw .incoherentCore

/-- Certify one slot: the scalar forms through the shared certifier, a group through this
    operator's own. -/
private def certifyDistinctCountOperand (model : FlatModel)
    (declaringGroup : GroupPath) (operand : ResolvedFieldEntityOperand model) :
    Except TemporalDistinctCountElabError
      (CheckedTemporalDistinctCountOperand model) :=
  match groupSlotSource? operand with
  | some source => certifyDistinctCountGroup model source
  | none =>
      (certifyTemporalUniquenessOperand model declaringGroup operand).map .slot
        |>.mapError .slot

private def certifyDistinctCountOperands (model : FlatModel)
    (declaringGroup : GroupPath) :
    List (ResolvedFieldEntityOperand model) →
      Except TemporalDistinctCountElabError
        (List (CheckedTemporalDistinctCountOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyDistinctCountOperand model declaringGroup operand) ::
        (← certifyDistinctCountOperands model declaringGroup remaining))

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
  let first ← certifyDistinctCountOperand model declaringGroup shape.first
  let rest ← certifyDistinctCountOperands model declaringGroup shape.rest
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
  | .incoherentCore => none

end TemporalDistinctCountElabError

end A12Kernel
