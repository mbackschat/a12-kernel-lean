import A12Kernel.Elaboration.Flat.Condition.SurfaceSupport
import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Elaboration.FieldEntityList

/-! # A12Kernel.Elaboration.TemporalExtremumOperands — admission for `MinValue`/`MaxValue` over temporal operands

[`Semantics/DateAggregate.lean`](../Semantics/DateAggregate.lean) folds an already-resolved temporal
stream. Nothing built that stream from a model, so the extrema over the temporal operands the Kernel
admits could not be constructed at all. This module supplies the half of that which does **not**
depend on the unresolved value domain: which operand lists the Kernel accepts.

**The gate reads the format's component set, not the format string, and not the declared kind.** Two
DATE fields declared `yyyy-MM-dd` and `dd.MM.yyyy` carry the same components under different
spellings and are admitted; so are `yyyy-MM` beside `yyyyMM`, a DATE beside a DATE_FRAGMENT at
`yyyy`, and a TIME beside a DATE_TIME declared with the degenerate time-only format. Component sets
that genuinely differ are refused. The sibling `FieldValuesNotUnique` carrier is the one whose gate
really is the declared format **string**, and reading its rule onto the extrema rejects legal
models — the two are measured to differ, so neither is derived from the other.

A declared **Base Year** supplies a missing year to a yearless operand before the comparison, which
is why `TemporalComponents.withBaseYear` is applied to both sides rather than tested as a special
case: a yearless `MM` then equals `yyyy-MM`, `MM-dd` equals a complete date, and both still differ
from a year-only operand, which is exactly the measured boundary.

Structure is delegated to the shared entity-list checker, so arity, the wildcard gate, and both
duplicate arms behave here exactly as they do for the sibling carriers, and a group or starred
operand is expressible; the component gate then reads a group's **expansion**, which is the extent
the Kernel's own gate reads.

Out of scope here, deliberately: the fold itself and therefore the value domain, filtered stars and
starred-group presence slots — which this capsule declines rather than admit without elaborating
their filter — and DATE_RANGE, whose allowlisted `(format, separator)` pair the Kernel treats the
same way but which this flat model gives no component set to compare.
-/

namespace A12Kernel

/-- Static refusal of a temporal extremum's operand list. -/
inductive TemporalExtremumOperandElabError where
  /-- Two operands' component sets differ after the Base Year is supplied to both. -/
  | incompatibleComponents (path : List String)
      (found expected : TemporalComponents)
  /-- A non-temporal operand. **No class is claimed**: the extrema admit Number, whose operands the Number entity list owns, so this arm means "not this family" and not "the Kernel refuses it". A String operand is separately measured to draw `MVK_NOT_SORTABLE`, but that verdict belongs to the kind gate rather than to this list. -/
  | notTemporal (path : List String) (actual : SurfaceScalarKind)
  /-- A group slot whose subtree declares no field, so no component set exists to agree on. -/
  | groupExpansionEmpty (path : List String)
  /-- A filtered star or a starred-group presence slot. Neither is refused by the Kernel; this capsule performs no filter elaboration, so it declines rather than admit one unchecked. -/
  | unsupportedOperandForm (path : List String)
  /-- The shared entity-list checker's own refusal: arity, the wildcard gate, and both duplicate arms. It is delegated rather than restated, because those gates do not vary by carrier. -/
  | shape (error : FieldEntityShapeElabError)
  deriving Repr, DecidableEq

/-- One admitted temporal operand list for an extremum, carrying the component set every member
    agrees on once the Base Year has been supplied.

    The retained `components` is the **lifted** set, so a consumer reads the set the operands were
    actually compared on rather than any one declaration's. -/
structure CheckedTemporalExtremumOperands (model : FlatModel) where
  shape : CheckedFieldEntityShape model
  components : TemporalComponents

namespace TemporalExtremumOperands

/-- The component set a declaration contributes, or `none` when it is not temporal. DATE_RANGE is
    excluded here with every other non-temporal kind, because this model carries no component set
    for it — a representation limit, not a Kernel verdict. -/
def componentsOf? (declaration : FlatFieldDecl) : Option TemporalComponents :=
  match declaration.policy.kind with
  | .temporal _ components => some components
  | _ => none

/-- Every declaration one resolved operand contributes, in expansion order. A group slot contributes
    its recursive subtree, which is what the Kernel's own gate reads; the two filtered forms are not
    expanded here because this capsule performs no filter elaboration and admitting one unchecked
    would be worse than refusing it. -/
private def operandDeclarations (model : FlatModel) :
    ResolvedFieldEntityOperand model →
      Except TemporalExtremumOperandElabError (List FlatFieldDecl)
  | .field declaration _ => pure [declaration]
  | .star source => pure [source.declaration]
  | .group reference =>
      match model.groupSubtreeFields reference.path with
      | [] => throw (.groupExpansionEmpty reference.path)
      | fields => pure fields
  | .starredGroup source =>
      match model.groupSubtreeFields source.group.path with
      | [] => throw (.groupExpansionEmpty source.group.path)
      | fields => pure fields
  | .starHaving source _ => throw (.unsupportedOperandForm source.declaration.path)
  | .starredGroupPresence source => throw (.unsupportedOperandForm source.groupPath)

private def liftedComponentsOf (model : FlatModel) (declaration : FlatFieldDecl) :
    Except TemporalExtremumOperandElabError TemporalComponents :=
  match componentsOf? declaration with
  | none =>
      throw (.notTemporal declaration.path declaration.policy.kind.surfaceKind)
  | some components =>
      pure (components.withBaseYear model.baseYear.isSome)

private def certifyAgainst (model : FlatModel) (expected : TemporalComponents) :
    List FlatFieldDecl → Except TemporalExtremumOperandElabError Unit
  | [] => pure ()
  | declaration :: rest => do
      let lifted ← liftedComponentsOf model declaration
      if lifted == expected then
        certifyAgainst model expected rest
      else
        throw (.incompatibleComponents declaration.path lifted expected)

/-- Admit one authored temporal extremum operand list.

    Structure delegates to the shared entity-list checker, so arity, the wildcard gate, and both duplicate arms behave here exactly as they do for the sibling carriers and a group or starred operand is expressible. What this capsule owns is the component-set gate on top of it, applied to every declaration each operand contributes — for a group, its whole recursive expansion, which is the extent the Kernel's own gate reads.

    The **first** contributed declaration fixes the expected set. That is a reporting choice rather than a semantic one: every later declaration must equal it, so the admitted lists are the same whichever member is read first, and only the path named in a refusal depends on the order. -/
def elaborate (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceFieldEntitySource) :
    Except TemporalExtremumOperandElabError
      (CheckedTemporalExtremumOperands model) := do
  let shape ←
    (elaborateFieldEntityShape model declaringGroup authored).mapError .shape
  let declarations ←
    (shape.first :: shape.rest).foldlM
      (fun accumulated operand => do
        pure (accumulated ++ (← operandDeclarations model operand)))
      ([] : List FlatFieldDecl)
  match declarations with
  | [] => throw (.groupExpansionEmpty [])
  | first :: rest =>
      let expected ← liftedComponentsOf model first
      certifyAgainst model expected rest
      pure { shape, components := expected }

end TemporalExtremumOperands

namespace TemporalExtremumOperandElabError

/-- Only the component-set refusal has an established class. The non-temporal arm is this family's own boundary rather than a Kernel gate, and an empty list is unauthorable rather than refused, so both project none. -/
def diagnostic? : TemporalExtremumOperandElabError → Option KernelStaticDiagnostic
  | .incompatibleComponents _ _ _ => some .dateFormatsNotCompatible
  | .notTemporal _ _ => none
  | .groupExpansionEmpty _ => none
  | .unsupportedOperandForm _ => none
  | .shape error => error.diagnostic?

end TemporalExtremumOperandElabError

end A12Kernel
