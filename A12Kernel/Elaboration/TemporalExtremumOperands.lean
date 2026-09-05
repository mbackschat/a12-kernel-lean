import A12Kernel.Elaboration.Flat.Condition.SurfaceSupport
import A12Kernel.Elaboration.Flat.Model

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

Out of scope here, deliberately: the fold itself and therefore the value domain, group and starred
operands, filters, and DATE_RANGE — whose allowlisted `(format, separator)` pair behaves the same way
at the Kernel but which this flat model gives no component set to compare.
-/

namespace A12Kernel

/-- Static refusal of a temporal extremum's operand list. -/
inductive TemporalExtremumOperandElabError where
  /-- Two operands' component sets differ after the Base Year is supplied to both. -/
  | incompatibleComponents (path : List String)
      (found expected : TemporalComponents)
  /-- A non-temporal operand. **No class is claimed**: the extrema admit Number, whose operands the Number entity list owns, so this arm means "not this family" and not "the Kernel refuses it". A String operand is separately measured to draw `MVK_NOT_SORTABLE`, but that verdict belongs to the kind gate rather than to this list. -/
  | notTemporal (path : List String) (actual : SurfaceScalarKind)
  /-- An empty operand list, which no authored extremum produces. -/
  | emptyOperands
  | resolve (error : ResolveError)
  deriving Repr, DecidableEq

/-- One admitted temporal operand list for an extremum, carrying the component set every member
    agrees on once the Base Year has been supplied.

    The retained `components` is the **lifted** set, so a consumer reads the set the operands were
    actually compared on rather than any one declaration's. -/
structure CheckedTemporalExtremumOperands (model : FlatModel) where
  first : FlatFieldDecl
  rest : List FlatFieldDecl
  components : TemporalComponents

namespace TemporalExtremumOperands

/-- The component set a declaration contributes, or `none` when it is not temporal. DATE_RANGE is
    excluded here with every other non-temporal kind, because this model carries no component set
    for it — a representation limit, not a Kernel verdict. -/
def componentsOf? (declaration : FlatFieldDecl) : Option TemporalComponents :=
  match declaration.policy.kind with
  | .temporal _ components => some components
  | _ => none

private def certifyOne (model : FlatModel) (expected : TemporalComponents)
    (declaration : FlatFieldDecl) :
    Except TemporalExtremumOperandElabError Unit :=
  match componentsOf? declaration with
  | none =>
      throw (.notTemporal declaration.path
        declaration.policy.kind.surfaceKind)
  | some components =>
      let lifted := components.withBaseYear model.baseYear.isSome
      if lifted == expected then
        pure ()
      else
        throw (.incompatibleComponents declaration.path lifted expected)

private def certifyRest (model : FlatModel) (expected : TemporalComponents) :
    List FlatFieldDecl → Except TemporalExtremumOperandElabError Unit
  | [] => pure ()
  | declaration :: rest => do
      certifyOne model expected declaration
      certifyRest model expected rest

/-- Admit one authored temporal extremum operand list.

    The **first** operand fixes the expected component set, which is a reporting choice and not a semantic one: every later operand must equal it, so the admitted lists are the same whichever member is read first. Only the path named in a refusal depends on the order. -/
def elaborate (model : FlatModel) (sources : List FieldId) :
    Except TemporalExtremumOperandElabError
      (CheckedTemporalExtremumOperands model) := do
  match sources with
  | [] => throw .emptyOperands
  | source :: rest =>
      let first ← (model.lookupUniqueId source).mapError .resolve
      let restDecls ←
        rest.mapM fun id => (model.lookupUniqueId id).mapError .resolve
      match componentsOf? first with
      | none =>
          throw (.notTemporal first.path first.policy.kind.surfaceKind)
      | some components =>
          let expected := components.withBaseYear model.baseYear.isSome
          certifyRest model expected restDecls
          pure { first, rest := restDecls, components := expected }

end TemporalExtremumOperands

namespace TemporalExtremumOperandElabError

/-- Only the component-set refusal has an established class. The non-temporal arm is this family's own boundary rather than a Kernel gate, and an empty list is unauthorable rather than refused, so both project none. -/
def diagnostic? : TemporalExtremumOperandElabError → Option KernelStaticDiagnostic
  | .incompatibleComponents _ _ _ => some .dateFormatsNotCompatible
  | .notTemporal _ _ => none
  | .emptyOperands => none
  | .resolve error => error.diagnostic?

end TemporalExtremumOperandElabError

end A12Kernel
