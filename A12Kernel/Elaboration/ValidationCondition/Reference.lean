import A12Kernel.Elaboration.ValidationCondition.Core
import A12Kernel.Semantics.MessagePointer

/-! # A12Kernel.Elaboration.ValidationCondition.Reference — structural message references

A fired validation message carries the field instances its rule *refers to*, and that collection is a **structural projection of the checked condition**, never a trace of which cells were read. This module is that projection. It takes the condition and the firing environment and nothing else: it has no document, context, or verdict argument, so it cannot degenerate into a read trace even by accident.

Coordinate assignment follows one rule. A repeatable level fixed by the rule's iteration scope is concrete at the firing instance; a level the star reopened, and every axis below it, is wildcard. Both facts are Kernel-locked upstream at a12-dmkits `bbbbf48e`; [`SOURCES.md`](../../../docs/SOURCES.md) owns that provenance.

Two boundaries are deliberate. Membership is total over the fragment it classifies and **fails closed everywhere else**, so an unsupported operand can never be silently read as "no reference". And this projection is not attached to `FlatRuleMessage`: the emitted record still has no reference channel, because a caller that holds a fired outcome also holds the rule and its environment. [`SG10`](../../../docs/SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration) owns the remaining channel work, the filtered-star operand, and the pointer-shape exclusion.
-/

namespace A12Kernel

/-- Why one structural reference projection has no answer. No case means an empty reference set: the leaf or atom family is outside the current fragment, a filtered star's operand coordinates are unpinned, the field does not resolve uniquely in the owning model, or the firing environment does not bind a level the reference needs. -/
inductive ReferenceProjectionError where
  | unclassifiedLeaf
  | unclassifiedAtom
  | filteredStarOperand
  | unresolvedField (field : FieldId)
  | binding (error : EnvBindingError)
  deriving Repr, DecidableEq

/-- Every repeatable level of an unstarred reference is fixed by the rule's iteration scope, so its pointer is the concrete instance the rule is evaluating. -/
def concreteFieldPointer (declaration : FlatFieldDecl) (environment : Env) :
    Except ReferenceProjectionError MessagePointer :=
  match environment.pathForScope declaration.repeatableScope with
  | .error error => .error (.binding error)
  | .ok path => .ok (MessagePointer.ofCellAddr { field := declaration.id, path })

/-- A starred reference keeps its bound prefix concrete and wildcards the reopened level together with every axis below it. The counts come from the checked path's own axes and `firstStar`, so nothing here re-derives repeatable scope. -/
def starFieldPointer (checked : CheckedStarFieldPath model) (environment : Env) :
    Except ReferenceProjectionError MessagePointer :=
  match environment.pathForScope checked.bindingScope with
  | .error error => .error (.binding error)
  | .ok bound => .ok {
      field := checked.declaration.id
      coordinates := bound.map .concrete ++
        List.replicate (checked.path.axes.length - checked.path.firstStar) .wildcard }

/-- A filtered star is refused rather than projected. Its own field pointer would be the plain starred one, but the measured account pins only that its `Having` operands *join* the set, not which coordinates they carry, and inventing them would make an incomplete set look complete. -/
def CheckedNumberEntityOperand.referencePointer (environment : Env) :
    CheckedNumberEntityOperand model →
      Except ReferenceProjectionError MessagePointer
  | .field source => concreteFieldPointer source.declaration environment
  | .star source => starFieldPointer source.source environment
  | .starHaving _ => .error .filteredStarOperand

/-- Every authored slot contributes, in authored order, whether or not a runtime scan would reach it. -/
def CheckedNumberEntitySource.referencePointers
    (source : CheckedNumberEntitySource model) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  source.operands.mapM (CheckedNumberEntityOperand.referencePointer environment)

/-- The classified atom fragment. Entity-list aggregates share one operand projection, and one direct Number field is admitted so that a mixed comparison can separate concrete from wildcard assignment. Every other shape, including the fieldless ones, fails closed. -/
def OrderedNumericValidationAtom.referencePointers (environment : Env) :
    OrderedNumericValidationAtom model →
      Except ReferenceProjectionError (List MessagePointer)
  | .ordinary (.field source) =>
      match model.lookupUniqueId source.id with
      | .error _ => .error (.unresolvedField source.id)
      | .ok declaration =>
          (concreteFieldPointer declaration environment).map ([·])
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      source.referencePointers environment
  | _ => .error .unclassifiedAtom

/-- Traverse one authored operand expression left to right. Literals reference nothing; a failing atom fails the whole projection. -/
private def expressionPointers (environment : Env) :
    AuthoredNumericExpr (OrderedNumericValidationAtom model) →
      Except ReferenceProjectionError (List MessagePointer)
  | .atom atom => atom.referencePointers environment
  | .literal _ => pure []
  | .group body | .abs body | .extremumCall _ body | .round _ _ body =>
      expressionPointers environment body
  | .binary _ left right | .power left right | .extremum _ left right => do
      pure ((← expressionPointers environment left) ++
        (← expressionPointers environment right))

def ValidationConditionLeaf.referencePointers (environment : Env) :
    ValidationConditionLeaf model →
      Except ReferenceProjectionError (List MessagePointer)
  | .orderedNumeric _ comparison => do
      pure ((← expressionPointers environment comparison.left) ++
        (← expressionPointers environment comparison.right))
  | _ => .error .unclassifiedLeaf

private def treePointers (environment : Env) :
    ValidationCondition model →
      Except ReferenceProjectionError (List MessagePointer)
  | .leaf value => value.referencePointers environment
  | .and left right | .or left right => do
      pure ((← treePointers environment left) ++
        (← treePointers environment right))

/-- The rule's structural reference set at one firing environment. Both connectives contribute every branch, because a reference exists by being authored rather than by being decisive.

    Duplicates are removed once. The retained order is authored traversal order and is **not** a kernel claim: the engine's own collection is a hash set whose iteration order is incidental, so a consumer may compare membership but never position. -/
def ValidationCondition.referencePointers (condition : ValidationCondition model)
    (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (treePointers environment condition).map List.eraseDups

end A12Kernel
