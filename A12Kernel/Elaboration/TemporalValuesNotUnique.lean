import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Semantics.NumericAggregate

/-! # Checked temporal `FieldValuesNotUnique`

The fourth comparability category of one operator. Slot admission, authored order, repeated-direct rejection, and the multiple-slots-or-one-star rule stay in `FieldEntityList`; the ordered fused scan and the whole polarity account stay in `NumericAggregate`. This module owns only what is temporal about the temporal overload: the admission gate and the compared identity.

**Admission** is one identical declared **format string** across every operand, keyed on the format rather than the kind. Real-kernel authoring accepts a DATE declared `yyyy` beside a DATE_FRAGMENT declared `yyyy` across two kinds while refusing two DATE fields differing only in declared format, so a kind-equality reading gets both directions wrong. Because a DATE_FRAGMENT is a `.date` declaration with a partial mode here, that cross-kind list is two `.temporal .date` operands whose partial modes differ and whose format agrees, and this gate admits it. Note that the kernel's two kinds therefore collapse to one at this boundary, so a local case can separate format equality from kind equality only in the refusing direction; the admitting direction separates it from whole-policy equality instead.

**The compared identity is the operand's exact stored text**, not its decoded value. That is what the *dynamic* kernel runtime reads for this operator, with the generated-Java strategy unread for this comparison, and it is deliberately a different reading from the decoded date that `NumberOfDifferentValues` uses over the same entity lists — the two neighbouring operators do not share a value identity. Under the mandatory single format the stored-text and decoded accounts agree *if* one declared format admits one text per value; that assumption is unmeasured and [`SG7`](../../docs/SEMANTICS-GAPS.md) owns its witness class. Reusing the canonical token atom is therefore exact rather than a rendering: the value compared is the stored text itself, so no normal form is invented.

Two admission facts are not modelled here and are annotations rather than gates. A declaration whose declared format disagrees with its own kind family is not refused by this gate, because format equality is stated as a total function and the authorability of such a declaration is unmeasured. And DATE_RANGE, which the kernel refuses by kind, has no representation in this flat model at all.
-/

namespace A12Kernel

inductive TemporalValuesNotUniqueElabError where
  | shape (error : FieldEntityShapeElabError)
  /-- An operand whose kind the operator refuses outright, which the Kernel's **first** gate reports. -/
  | inadmissibleKind (path : List String) (actual : SurfaceScalarKind)
  /-- An operand of an individually admissible kind drawn from another comparability category, which the Kernel's **second** gate reports. -/
  | mixedCategories (path : List String) (actual : SurfaceScalarKind)
  /-- A temporal operand whose declaration carries no coherent declared format. The operator's gate and its compared identity both need the exact format, so an incomplete declaration fails closed rather than defaulting. -/
  | missingDeclaredFormat (path : List String)
  | mixedDeclaredFormats (path : List String) (found expected : String)
  | having (error : CorrelationElabError)
  /-- The shared checker admitted a group-scope slot that this family does not yet retain. Deliberately carries no diagnostic class: the Kernel admits the operand here, so a refusal states only that the representation is missing. -/
  | groupOperandNotRepresented (path : List String)
  deriving Repr, DecidableEq

/-- One temporal declaration admitted by this operator, carrying the exact declared format its admission gate reads. -/
structure CheckedTemporalUniquenessField where
  private mk ::
  declaration : FlatFieldDecl
  policy : TemporalTargetPolicy
  policyOwned : declaration.toTemporalTargetPolicy? = some policy
  deriving Repr

namespace CheckedTemporalUniquenessField

def format (checked : CheckedTemporalUniquenessField) : String :=
  checked.policy.format

def path (checked : CheckedTemporalUniquenessField) : List String :=
  checked.declaration.path

end CheckedTemporalUniquenessField

/-- Certify one resolved declaration as a temporal operand. A non-temporal kind and a temporal kind without a coherent declared format are distinct refusals: the first is the wrong comparability category, the second an insufficient declaration. -/
def certifyTemporalUniquenessField (declaration : FlatFieldDecl) :
    Except TemporalValuesNotUniqueElabError CheckedTemporalUniquenessField :=
  match hPolicy : declaration.toTemporalTargetPolicy? with
  | some policy => .ok { declaration, policy, policyOwned := hPolicy }
  | none =>
      let kind := declaration.policy.kind.surfaceKind
      match kind.fieldListAdmission with
      | .category .temporal => .error (.missingDeclaredFormat declaration.path)
      | .category _ => .error (.mixedCategories declaration.path kind)
      | .refusedByKind => .error (.inadmissibleKind declaration.path kind)

/-- One certified temporal slot. A filter belongs to its exact authored wildcard occurrence. -/
inductive CheckedTemporalUniquenessOperand (model : FlatModel) where
  | field (source : CheckedTemporalUniquenessField)
  | star (path : CheckedStarFieldPath model)
      (source : CheckedTemporalUniquenessField)
      (filter : Option CorrelatedHaving)

namespace CheckedTemporalUniquenessOperand

def source : CheckedTemporalUniquenessOperand model →
    CheckedTemporalUniquenessField
  | .field source | .star _ source _ => source

def format (operand : CheckedTemporalUniquenessOperand model) : String :=
  operand.source.format

def path (operand : CheckedTemporalUniquenessOperand model) : List String :=
  operand.source.path

def hasHaving : CheckedTemporalUniquenessOperand model → Bool
  | .field _ | .star _ _ none => false
  | .star _ _ (some _) => true

/-- Resolve one slot against the immutable checked document through the shared kind-neutral entity core, which owns topology, addressing, filter selection, and omitted-tail extent. -/
def resolveValidationCore (operand : CheckedTemporalUniquenessOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore :=
  match operand with
  | .field source =>
      document.resolveCheckedDirectEntityOperandCore source.declaration.id
  | .star path _ filter =>
      path.resolveCheckedValidationEntityOperandCore document outer filter

end CheckedTemporalUniquenessOperand

/-- Find the first operand whose declared format differs from the list's, reporting its path and both formats. Public because the certificate below states its gate in terms of this scan, so an external law has to speak about it. -/
def firstMismatchedTemporalFormat? (expected : String) :
    List (CheckedTemporalUniquenessOperand model) →
      Option (List String × String)
  | [] => none
  | operand :: remaining =>
      if operand.format == expected then
        firstMismatchedTemporalFormat? expected remaining
      else
        some (operand.path, operand.format)

/-- One checked temporal `FieldValuesNotUnique` operand list, certified to carry a single declared format. -/
structure CheckedTemporalValuesNotUniqueSource (model : FlatModel) where
  private mk ::
  /-- The shared shape this list was certified from. It carries model validity, the multiple-slots-or-one-star rule, and repeated-direct rejection; `first`/`rest` are its own slots certified in the same order. -/
  shape : CheckedFieldEntityShape model
  first : CheckedTemporalUniquenessOperand model
  rest : List (CheckedTemporalUniquenessOperand model)
  oneDeclaredFormat :
    firstMismatchedTemporalFormat? first.format rest = none

namespace CheckedTemporalValuesNotUniqueSource

def operands (checked : CheckedTemporalValuesNotUniqueSource model) :
    List (CheckedTemporalUniquenessOperand model) :=
  checked.first :: checked.rest

/-- The list's single declared format, which every operand shares by construction. -/
def format (checked : CheckedTemporalValuesNotUniqueSource model) : String :=
  checked.first.format

end CheckedTemporalValuesNotUniqueSource

private def certifyTemporalUniquenessOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except TemporalValuesNotUniqueElabError
        (CheckedTemporalUniquenessOperand model)
  | .field declaration _ =>
      do pure (.field (← certifyTemporalUniquenessField declaration))
  | .star source =>
      do pure (.star source (← certifyTemporalUniquenessField source.declaration)
        none)
  | .starHaving source having => do
      let field ← certifyTemporalUniquenessField source.declaration
      let filter ← elaborateStarHavingCore model declaringGroup source having
        |>.mapError .having
      pure (.star source field (some filter.condition))
  | .group reference => throw (.groupOperandNotRepresented reference.path)
  | .starredGroup source =>
      throw (.groupOperandNotRepresented source.group.path)

private def certifyTemporalUniquenessOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except TemporalValuesNotUniqueElabError
        (List (CheckedTemporalUniquenessOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyTemporalUniquenessOperand model declaringGroup operand) ::
        (← certifyTemporalUniquenessOperands model declaringGroup remaining))

/-- Report the first operand the Kernel's **kind** gate refuses, scanning the whole list. This runs before any category or format decision because the gate order is observable: a Boolean or Confirm beside a String reports the kind code with the mixing code absent. Public because the gate-order law has to speak about this scan. -/
def firstKindGateRefusal? :
    List (ResolvedFieldEntityOperand model) →
      Option TemporalValuesNotUniqueElabError
  | operands =>
      match firstFieldListKindRefusal? operands with
      | some refusal => some (.inadmissibleKind refusal.path refusal.actual)
      | none => none

/-- Admit one temporal operand list in the Kernel's gate order: the shared entity shape, then the kind gate over every operand, then the single-declared-format rule that shares the kind gate's code, and only then the category-mixing gate that certification reports. -/
def elaborateTemporalValuesNotUniqueSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except TemporalValuesNotUniqueElabError
      (CheckedTemporalValuesNotUniqueSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  match firstKindGateRefusal? shape.operands with
  | some refusal => throw refusal
  | none => pure ()
  let first ← certifyTemporalUniquenessOperand model declaringGroup shape.first
  let rest ← certifyTemporalUniquenessOperands model declaringGroup shape.rest
  match hFormats : firstMismatchedTemporalFormat? first.format rest with
  | some (path, found) =>
      throw (.mixedDeclaredFormats path found first.format)
  | none => pure { shape, first, rest, oneDeclaredFormat := hFormats }

namespace TemporalValuesNotUniqueElabError

/-- The Kernel diagnostic class this refusal corresponds to, or `none` where this project refuses a shape whose Kernel class it has not established.

`none` is deliberate rather than a placeholder: `missingDeclaredFormat` is this project's own insufficiency for a declaration the Kernel rejects earlier at model level with an unmeasured code, a group-scope slot is admitted by the Kernel and merely unrepresented here, and a filter failure belongs to the correlation surface. Mapping any of them to a plausible-looking name would assert an unmeasured correspondence. Every shape refusal delegates to the shared checker's own projection, because the star, arity, and duplicate gates do not vary by carrier. -/
def diagnostic? : TemporalValuesNotUniqueElabError → Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .inadmissibleKind _ _ => some .onlyStringEnumNumberDateAllowed
  -- The temporal format rule lives inside the same Kernel predicate as the kind gate and reports
  -- its code, which is why a cross-temporal list reports it rather than the mixing code.
  | .mixedDeclaredFormats _ _ _ => some .onlyStringEnumNumberDateAllowed
  | .mixedCategories _ _ => some .varyingTypesNotAllowed
  | .missingDeclaredFormat _ => none
  | .groupOperandNotRepresented _ => none
  | .having _ => none

end TemporalValuesNotUniqueElabError

/-- Project one addressed temporal cell to its compared identity. The decoded value is deliberately discarded in favour of the exact stored text; empty and formally unavailable cells keep their own states, because this operator skips both alike. -/
private def temporalUniquenessCell (addressed : CheckedAddressedCell) :
    ValueListCell .token :=
  match observeCell .validation addressed.cell, addressed.stored with
  | .value _, some text => .present text
  -- Unreachable for a checked document: a parsed cell has a physical placement and
  -- therefore stored text. Skipping is the conservative projection if it ever were.
  | .value _, none => .empty
  | .empty, _ => .empty
  | .unknown cause, _ | .poison cause, _ => .unknown cause

namespace CheckedTemporalValuesNotUniqueSource

/-- Evaluate the temporal uniqueness predicate from one immutable model-certified checked document. Slots resolve in authored order and every reached cell reaches the scan, because this operator skips a formally unavailable cell instead of suppressing on it. -/
def evaluateCheckedDocumentValuesNotUnique
    (checked : CheckedTemporalValuesNotUniqueSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError Verdict := do
  let tagged ← collectTaggedValueListCells
    (fun operand => do
      let core ← operand.resolveValidationCore document outer
      pure {
        cells := core.addressedCells.map temporalUniquenessCell
        hasUninstantiatedTail := core.hasUninstantiatedTail
        hasHaving := core.hasHaving
        hasNonRelevant := core.hasNonRelevant })
    checked.operands
  pure (evalValuesNotUniqueVerdict tagged)

end CheckedTemporalValuesNotUniqueSource

end A12Kernel
