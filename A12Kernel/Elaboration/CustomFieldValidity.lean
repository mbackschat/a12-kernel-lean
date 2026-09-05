import A12Kernel.Elaboration.Flat.Condition.SurfaceSupport
import A12Kernel.Elaboration.Flat.Context
import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Semantics.CustomFieldValidity

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

    `unmeasuredKind` is deliberately separate from `inadmissibleKind` rather than folded into it: both are refusals, but only the second has a Kernel class established for it, and merging them would let an unmeasured kind report a code this project never observed. -/
inductive CustomFieldValidityOperandElabError where
  /-- A declared kind the Kernel is measured to refuse at this slot: Number, Boolean, Confirm. -/
  | inadmissibleKind (source : FieldId) (actual : SurfaceScalarKind)
  /-- A String declaration carrying a registered custom type. Refused, and measured. -/
  | customDeclaredOperand (source : FieldId)
  /-- A declared kind outside the admitted set whose refusal class was never observed here: the temporal kinds and DateRange. Refused on the strength of the Kernel's own admitted-set text, with no class claimed. -/
  | unmeasuredKind (source : FieldId) (actual : SurfaceScalarKind)
  /-- A raw String, which exposes no evaluation value and so could not reach a validator. A representation limit of this theory, not an observed Kernel gate; see the module note on the spec's *value-validation* qualifier. -/
  | rawStringOperand (source : FieldId)
  | resolve (error : ResolveError)
  deriving Repr, DecidableEq

/-- One field declaration admitted into a value-validation predicate's operand slot.

    The retained declaration is what a later runtime clause reads the observation from; nothing here chooses that projection, and for an Enumeration operand it is still open which of the stored token and the display label the validator receives. -/
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
      | .number | .boolean | .confirm =>
          throw (.inadmissibleKind source declaration.policy.kind.surfaceKind)
      | .temporal _ | .dateRange =>
          throw (.unmeasuredKind source declaration.policy.kind.surfaceKind)

namespace CustomFieldValidityOperandElabError

/-- Project only the classes measured at this slot. The unmeasured kinds and this theory's own raw-String limit claim none, which is this vocabulary's honest state for an unestablished mapping. -/
def diagnostic? : CustomFieldValidityOperandElabError → Option KernelStaticDiagnostic
  | .inadmissibleKind _ _ => some .noStringOrEnumOrExtEnum
  | .customDeclaredOperand _ => some .noStringOrEnumOrExtEnum
  | .unmeasuredKind _ _ => none
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

def elaborateCustomFieldValidityLeaf (model : FlatModel) (world : World)
    (source : FieldId) (name : String) (operation : CustomFieldValidityOp) :
    Except CustomFieldValidityLeafElabError
      (CheckedCustomFieldValidityLeaf model) := do
  let operand ←
    (elaborateCustomFieldValidityOperand model source).mapError .operand
  let validity ← (elaborateCustomFieldValidity world name).mapError .name
  pure { operand, validity, operation }

namespace CheckedCustomFieldValidityLeaf

/-- Evaluate the predicate against one flat context.

    The operand is read through the **checked** observation, so a formally invalid cell reaches the predicate as unavailable and never reaches the validator: a validator answering about the stored text of a cell the rest of the theory cannot read would contradict every other consumer of that cell.

    `CellObservation.asText` maps a non-String payload to formally unavailable rather than absent. It sits beside the observation type because the semantic index's exact-text key read needs the identical meaning; this is its second user.

    **This function decides nothing about an Enumeration operand.** It forwards whatever payload the context's checked cell carries, so which text a validator sees for an Enumeration — the stored token or the display value — stays the caller's, and remains the open half of this family rather than being settled here by the projection's shape. -/
def evalAt (leaf : CheckedCustomFieldValidityLeaf model)
    (context : FlatContext) (phase : Phase) : Verdict :=
  leaf.validity.eval leaf.operation
    (context.observeAt phase leaf.operand.source).asText

end CheckedCustomFieldValidityLeaf

end A12Kernel
