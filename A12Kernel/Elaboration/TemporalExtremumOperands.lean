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

**The family itself is chosen by the first operand, and that makes position semantic.** If the first
operand is temporal every later one must be too, and a Number or String there draws
`MVK_DATE_AND_NONDATE`; if the first is not temporal the list is the Number family's and its own
refusal, `MVK_NOT_SORTABLE`, is what the Kernel reports. So the *same two operands* in the other
order draw a different code, and an arm that keyed on the offending kind alone would be right in one
order and wrong in the other. The distinct count was already measured to select its class the same
way, so this is one mechanism across the entity-list operators rather than a rule of the extrema.

A declared **Base Year** supplies a missing year to a yearless operand before the comparison, which
is why `TemporalComponents.withBaseYear` is applied to both sides rather than tested as a special
case: a yearless `MM` then equals `yyyy-MM`, `MM-dd` equals a complete date, and both still differ
from a year-only operand, which is exactly the measured boundary.

Structure is delegated to the shared entity-list checker, so arity, the wildcard gate, and both
duplicate arms behave here exactly as they do for the sibling carriers, and a group or starred
operand is expressible; the component gate then reads a group's **expansion**, which is the extent
the Kernel's own gate reads.

A `Having`-filtered star is an operand like any other here, because the filter selects rows and the
gate reads fields; the measured rows confirm it against both a matching and a differing set.

Out of scope here, deliberately: the fold itself and therefore the value domain, starred-group
presence slots — which this capsule declines rather than admit unmeasured — and DATE_RANGE, whose
allowlisted `(format, separator)` pair the Kernel treats the same way but which this flat model
gives no component set to compare.
-/

namespace A12Kernel

/-- Static refusal of a temporal extremum's operand list. -/
inductive TemporalExtremumOperandElabError where
  /-- Two operands' component sets differ after the Base Year is supplied to both. -/
  | incompatibleComponents (path : List String)
      (found expected : TemporalComponents)
  /-- The list's **first** operand is not temporal, so it is not this family's list at all. **No class is claimed**: the extrema admit Number, whose operands the Number entity list owns, and that list draws its own code. -/
  | firstNotTemporal (path : List String) (actual : SurfaceScalarKind)
  /-- A **later** operand is not temporal after a temporal first one. This is the Kernel's own refusal, `MVK_DATE_AND_NONDATE`, and its text states the positional rule outright. -/
  | laterNotTemporal (path : List String) (actual : SurfaceScalarKind)
  /-- A group slot whose subtree declares no field, so no component set exists to agree on. -/
  | groupExpansionEmpty (path : List String)
  /-- A starred-group **presence** slot. This capsule declines it rather than admit it unchecked,
      and the decline **claims no Kernel class**: whether the Kernel admits the form at this carrier
      is unmeasured. Stated that way on purpose — the neighbouring DateRange-endpoint carrier
      refuses a starred operand outright with `MVK_NO_WILDCARDS_ALLOWED`
      ([`spec/05`](../../spec/05-dates-and-time.md#8-date-ranges-and-overlap)), so the carrier
      boundary is known to be real and reading this one off the extremum's plain-star admission
      would be the crossing declined elsewhere in this family
      ([`LF116`](../../docs/LEAN-FINDINGS.md)).

      The filtered star shared this arm until its own measurement arrived and admitted it, which is
      the reason to keep the two declines separable rather than merged under one "unsupported"
      heading: they were never one question. -/
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
    its recursive subtree, which is what the Kernel's own gate reads.

    A `Having`-filtered star contributes exactly what its unfiltered form does. The filter selects
    **rows**, never fields, so it cannot reach the component set of the field being read — and the
    Kernel agrees: the filtered star is admitted wherever the plain one is and draws the identical
    incompatibility against a differing set, in either operand position
    ([checkpoint](../../docs/SOURCES.md#src-filtered-star-temporal-carriers-and-binding-depth)).
    No filter elaboration happens here because none is needed for this gate; the filter's own
    legality is the entity-list checker's business, delegated with every other shape gate. -/
private def operandDeclarations (model : FlatModel) :
    ResolvedFieldEntityOperand model →
      Except TemporalExtremumOperandElabError (List FlatFieldDecl)
  | .field declaration _ => pure [declaration]
  | .star source | .starHaving source _ => pure [source.declaration]
  | .group reference =>
      match model.groupSubtreeFields reference.path with
      | [] => throw (.groupExpansionEmpty reference.path)
      | fields => pure fields
  | .starredGroup source =>
      match model.groupSubtreeFields source.group.path with
      | [] => throw (.groupExpansionEmpty source.group.path)
      | fields => pure fields
  | .starredGroupPresence source => throw (.unsupportedOperandForm source.groupPath)

/-- The lifted component set of one declaration, or the refusal its **position** earns. The two
    positions draw different Kernel codes and the caller alone knows which it is holding, so the
    position is a parameter here rather than a second function. -/
private def liftedComponentsOf (model : FlatModel) (isFirst : Bool)
    (declaration : FlatFieldDecl) :
    Except TemporalExtremumOperandElabError TemporalComponents :=
  match componentsOf? declaration with
  | none =>
      let kind := declaration.policy.kind.surfaceKind
      if isFirst then
        throw (.firstNotTemporal declaration.path kind)
      else
        throw (.laterNotTemporal declaration.path kind)
  | some components =>
      pure (components.withBaseYear model.baseYear.isSome)

private def certifyAgainst (model : FlatModel) (expected : TemporalComponents) :
    List FlatFieldDecl → Except TemporalExtremumOperandElabError Unit
  | [] => pure ()
  | declaration :: rest => do
      let lifted ← liftedComponentsOf model false declaration
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
      let expected ← liftedComponentsOf model true first
      certifyAgainst model expected rest
      pure { shape, components := expected }

end TemporalExtremumOperands

namespace TemporalExtremumOperandElabError

/-- Two refusals carry a Kernel class, and they are told apart by operand **position** rather than by kind. A first non-temporal operand means the authored list is the Number family's, whose own list draws `MVK_NOT_SORTABLE`, so this arm claims nothing. An empty expansion is unauthorable rather than refused. -/
def diagnostic? : TemporalExtremumOperandElabError → Option KernelStaticDiagnostic
  | .incompatibleComponents _ _ _ => some .dateFormatsNotCompatible
  | .firstNotTemporal _ _ => none
  -- Measured for a Number and for a String in later position; the remaining four kinds are not,
  -- and the Kernel's own generalizing text is its wording rather than an observation.
  | .laterNotTemporal _ actual =>
      match actual with
      | .number | .string => some .dateAndNonDate
      | .temporal _ | .enumeration | .boolean | .confirm | .dateRange => none
  | .groupExpansionEmpty _ => none
  | .unsupportedOperandForm _ => none
  | .shape error => error.diagnostic?

end TemporalExtremumOperandElabError

end A12Kernel
