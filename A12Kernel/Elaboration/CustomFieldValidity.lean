import A12Kernel.Elaboration.Flat.Condition.SurfaceSupport
import A12Kernel.Elaboration.Flat.Context
import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Semantics.CustomFieldValidity
import A12Kernel.Elaboration.SemanticIndex

/-! # A12Kernel.Elaboration.CustomFieldValidity — the operand slot of the explicit validity predicates

[`Semantics/CustomFieldValidity.lean`](../Semantics/CustomFieldValidity.lean) owns what
`Valid(field, "Name")` and `Invalid(field, "Name")` *do* with a String observation and a resolved
validator. This module owns the other half of their static contract: **which declaration may fill
the field slot at all.**

The slot takes a single unstarred field, so a group operand and a starred one are refused by the
Kernel with their own classes and are simply not expressible in this signature, the same idiom
`ValueAsDate` uses. What *is* expressible, and is the whole content here, is the declaration's
kind.

**The Custom-typed operand is the arm worth having a module for.** The predicate names a custom
type, so a field already declared with a `CustomFieldType` is the operand a reader expects it to
accept, and the Kernel refuses it: the predicate asks whether a String or Enumeration *value* is a
valid instance of a named type, not whether a field is already of that shape. In this project's
flat model such a field is a String declaration carrying `customType`, so the gate cannot be read
off `policy.kind` alone.
-/

namespace A12Kernel

/-- Static refusal of the value-validation operand slot.

    A separate `unmeasuredKind` arm stood here while only some refused kinds had an established class. Every refused kind is now measured onto the **same** class, so the split had no remaining content and folding it removes a distinction the Kernel does not draw. -/
inductive CustomFieldValidityOperandElabError where
  /-- A declared kind the Kernel is measured to refuse at this slot: Number, Boolean, Confirm. -/
  | inadmissibleKind (source : FieldId) (actual : SurfaceScalarKind)
  /-- A String declaration carrying a registered custom type. Refused, and measured. -/
  | customDeclaredOperand (source : FieldId)
  /-- A raw String, which exposes no evaluation value and so could not reach a validator. A representation limit of this theory, not an observed Kernel gate; see the module note on the spec's *value-validation* qualifier. -/
  | rawStringOperand (source : FieldId)
  | resolve (error : ResolveError)
  deriving Repr, DecidableEq

/-- One field declaration admitted into a value-validation predicate's operand slot.

    The retained declaration owns the checked observation. Enumeration evaluation passes its stored token to the named validator, as the runtime’s XML-value read requires. -/
structure CheckedCustomFieldValidityOperand (model : FlatModel) where
  source : FieldId
  declaration : FlatFieldDecl
  admitted : model.lookupUniqueId source = .ok declaration

/-- Admit one value-validation operand by its declared kind.

    Extensible Enumeration is admitted with ordinary Enumeration and not separated, because this flat model carries no extensible variant to separate it with. -/
def elaborateCustomFieldValidityOperand (model : FlatModel) (source : FieldId) :
    Except CustomFieldValidityOperandElabError
      (CheckedCustomFieldValidityOperand model) :=
  match hDecl : model.lookupUniqueId source with
  | .error error => throw (.resolve error)
  | .ok declaration =>
      match declaration.policy.kind.surfaceKind with
      | .string | .enumeration =>
          -- Both further gates read a String declaration and neither can fire on the other's
          -- input: the model check already forbids a raw String from carrying a custom type
          -- (`rawValueModeForbidsCustomType`), so their order asserts no precedence.
          if declaration.customType.isSome then
            throw (.customDeclaredOperand source)
          else if declaration.isRawString then
            throw (.rawStringOperand source)
          else
            pure { source, declaration, admitted := hDecl }
      -- Every kind outside the admitted set draws one class, the temporal families and DATE_RANGE
      -- included, so this gate names the admitted set rather than partitioning the refused ones
      -- ([checkpoint](../../docs/SOURCES.md#src-custom-validity-operand-refuses-every-kind-with-one-class)).
      | .number | .boolean | .confirm | .temporal _ | .dateRange =>
          throw (.inadmissibleKind source declaration.policy.kind.surfaceKind)

namespace CustomFieldValidityOperandElabError

/-- Every kind refusal at this slot draws one class. Only this theory's own raw-String limit claims none, because it is a representation boundary rather than an observed Kernel gate. -/
def diagnostic? : CustomFieldValidityOperandElabError → Option KernelStaticDiagnostic
  | .inadmissibleKind _ _ => some .noStringOrEnumOrExtEnum
  | .customDeclaredOperand _ => some .noStringOrEnumOrExtEnum
  | .rawStringOperand _ => none
  | .resolve error => error.diagnostic?

end CustomFieldValidityOperandElabError

/-- Static refusal of a whole validity leaf. The two arms are independent gates, and their **order here asserts no precedence**: the nonempty-type-name refusal has never been observed beside an inadmissible operand, so which one the Kernel reports first is unmeasured. -/
inductive CustomFieldValidityLeafElabError where
  | operand (error : CustomFieldValidityOperandElabError)
  | name (error : CustomFieldValidityElabError)
  deriving Repr, DecidableEq

/-- One complete explicit validity predicate: an admitted operand, the resolution outcome for its authored type name, and the polarity. This is what makes the family evaluable from a model and a context rather than from a hand-built observation. -/
structure CheckedCustomFieldValidityLeaf (model : FlatModel) where
  operand : CheckedCustomFieldValidityOperand model
  validity : CheckedCustomFieldValidity
  operation : CustomFieldValidityOp

/-- A selected value retains the original operand admission; selection cannot change its target
(spec/06 named-type validity and spec/08 §4). -/
structure CheckedIndexedCustomFieldValidityOperand (model : FlatModel) where
  selection : CheckedSemanticIndexSource model
  operand : CheckedCustomFieldValidityOperand model
  sameTarget : selection.targetDeclaration.id = operand.source

inductive IndexedCustomFieldValidityElabError where
  | selection (error : SemanticIndexElabError)
  | operand (error : CustomFieldValidityOperandElabError)
  | name (error : CustomFieldValidityElabError)
  | incoherent
  deriving Repr, DecidableEq

def elaborateIndexedCustomFieldValidityOperand (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceSemanticIndex) :
    Except IndexedCustomFieldValidityElabError (CheckedIndexedCustomFieldValidityOperand model) := do
  let selection ← (elaborateSemanticIndexSource model rowGroup surface).mapError .selection
  let operand ← (elaborateCustomFieldValidityOperand model selection.targetDeclaration.id).mapError .operand
  if sameTarget : selection.targetDeclaration.id = operand.source then
    pure { selection, operand, sameTarget }
  else throw .incoherent

def CheckedIndexedCustomFieldValidityOperand.bindingScope
    (source : CheckedIndexedCustomFieldValidityOperand model) : List RepeatableLevel :=
  match source.selection.key with
  | .literal .. => []
  | .field declaration => declaration.repeatableScope

structure CheckedIndexedCustomFieldValidityLeaf (model : FlatModel) where
  source : CheckedIndexedCustomFieldValidityOperand model
  validity : CheckedCustomFieldValidity
  operation : CustomFieldValidityOp

def CheckedIndexedCustomFieldValidityLeaf.directLeaf
    (leaf : CheckedIndexedCustomFieldValidityLeaf model) : CheckedCustomFieldValidityLeaf model :=
  { operand := leaf.source.operand, validity := leaf.validity, operation := leaf.operation }

def elaborateIndexedCustomFieldValidityLeaf (model : FlatModel) (rowGroup : GroupPath)
    (world : World) (source : SurfaceSemanticIndex) (name : String) (operation : CustomFieldValidityOp) :
    Except IndexedCustomFieldValidityElabError (CheckedIndexedCustomFieldValidityLeaf model) := do
  let source ← elaborateIndexedCustomFieldValidityOperand model rowGroup source
  let validity ← (elaborateCustomFieldValidity world name).mapError .name
  pure { source, validity, operation }

def elaborateCustomFieldValidityLeaf (model : FlatModel) (world : World)
    (source : FieldId) (name : String) (operation : CustomFieldValidityOp) :
    Except CustomFieldValidityLeafElabError
      (CheckedCustomFieldValidityLeaf model) := do
  let operand ←
    (elaborateCustomFieldValidityOperand model source).mapError .operand
  let validity ← (elaborateCustomFieldValidity world name).mapError .name
  pure { operand, validity, operation }

namespace CheckedCustomFieldValidityLeaf

/-- Evaluate the predicate against one checked observation.

    The operand is read through the **checked** observation, so a formally invalid cell reaches the predicate as unavailable and never reaches the validator: a validator answering about the stored text of a cell the rest of the theory cannot read would contradict every other consumer of that cell.

    `CellObservation.asText` preserves String availability and refuses unrelated payloads. Enumeration tokens use their own admitted projection before that fallback.

    Enumeration cells retain their stored token. RuntimeController’s predefined-type predicates read the XML value, so display labels must not replace that token (source checkpoint: named-type computation guards, 2026-10-04).

    Scalar, selected and addressed partial reads share this projection, so a covered cell gets one answer by construction rather than by separate arms happening to agree. -/
def evalObservation (leaf : CheckedCustomFieldValidityLeaf model)
    (observation : CellObservation) : Verdict :=
  leaf.validity.eval leaf.operation (match observation with
    | .value (.enum token) => .value token
    | other => other.asText)

def evalCell (leaf : CheckedCustomFieldValidityLeaf model) (phase : Phase)
    (cell : CheckedCell) : Verdict :=
  leaf.evalObservation (observeCell phase cell)

/-- Evaluate the predicate against one flat context, reading its own operand. -/
def evalAt (leaf : CheckedCustomFieldValidityLeaf model)
    (context : FlatContext) (phase : Phase) : Verdict :=
  leaf.evalCell phase (context.read leaf.operand.source)

end CheckedCustomFieldValidityLeaf

end A12Kernel
