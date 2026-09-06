import A12Kernel.Elaboration.TokenEntityValueList

/-! # A12Kernel.Conformance.ValueListQuantifierKindGate — which field kinds a String-literal value list admits

The three plural value-list quantifiers compare a field list against String literals, and their
kind gate partitions **three** ways rather than two. That third class is invisible to a reading
that sorts kinds into admitted and refused, and it is the operator's own message vocabulary that
makes it legible: a Number field is *inside* the set `MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED` names,
so it passes that gate and then fails the **literal** comparison with
`MVK_INVALID_TYPES_FOR_COMPARISON`, where DATE, BOOLEAN, DATE_RANGE and CONFIRM never reach that
stage ([checkpoint](../../docs/SOURCES.md#src-value-list-quantifier-kind-gate-partitions-three-ways)).
Collapsing the two would report the admitted-set class for a kind the Kernel calls admitted.

The rows use same-kind **pairs**. This carrier's shared shape gate demands two operands, while the
Kernel admits a sole field here and refuses one at the entity-list carriers — a per-carrier arity
divergence this project does not yet represent, recorded in the checkpoint above and in
[SG8](../../docs/SEMANTICS-GAPS.md). Pairs reach the kind gate without arguing with the arity one.
-/

namespace A12Kernel.Conformance.ValueListQuantifierKindGate

open A12Kernel

/-- One declaration per kind the gate can receive, in same-kind pairs. -/
private def probeModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe"], name := "Email",
        policy := { kind := .string } },
      { id := 2, groupPath := ["Probe"], name := "Phone",
        policy := { kind := .string } },
      { id := 3, groupPath := ["Probe"], name := "AVal",
        policy := { kind := .number { scale := 0, signed := false } } },
      { id := 4, groupPath := ["Probe"], name := "BVal",
        policy := { kind := .number { scale := 0, signed := false } } },
      { id := 5, groupPath := ["Probe"], name := "ReportedOn",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
      { id := 6, groupPath := ["Probe"], name := "SettledOn",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
      { id := 7, groupPath := ["Probe"], name := "Flag",
        policy := { kind := .boolean } },
      { id := 8, groupPath := ["Probe"], name := "Flag2",
        policy := { kind := .boolean } },
      { id := 9, groupPath := ["Probe"], name := "Agreed",
        policy := { kind := .confirm } },
      { id := 10, groupPath := ["Probe"], name := "Agreed2",
        policy := { kind := .confirm } },
      { id := 11, groupPath := ["Probe"], name := "Span",
        policy := { kind := .dateRange },
        dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
      { id := 12, groupPath := ["Probe"], name := "Span2",
        policy := { kind := .dateRange },
        dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
      { id := 13, groupPath := ["Probe"], name := "Choice",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["A", "B"] } },
      { id := 14, groupPath := ["Probe"], name := "Choice2",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["A", "B"] } }] }

example : probeModel.validate.isOk = true := by native_decide

private inductive Admission where
  | admitted
  | refused (diagnostic : Option KernelStaticDiagnostic)
  deriving Repr, DecidableEq

private def field (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups := ["Probe"], field := name }

private def pairAdmission (a b : String) : Admission :=
  match elaborateTokenEntityStringLiteralValueListSource probeModel ["Probe"]
      { quantifier := .atLeastOne
        fields := { first := field a, rest := [field b] }
        values := ["x", "y"] } with
  | .ok _ => .admitted
  | .error error => .refused error.diagnostic?

/- The admitted kind, which keeps the refusals below from reading as "this operator refuses
   fields". -/
example : pairAdmission "Email" "Phone" = .admitted := by native_decide

/- The middle class: admitted by the kind gate, refused by the literal comparison. -/
example :
    pairAdmission "AVal" "BVal" = .refused (some .invalidTypesForComparison) := by
  native_decide

/- The four kinds outside the admitted set, which never reach that comparison. Asserted together
   because the property is that they share one class, not that each has one. -/
example :
    [pairAdmission "ReportedOn" "SettledOn", pairAdmission "Flag" "Flag2",
      pairAdmission "Span" "Span2", pairAdmission "Agreed" "Agreed2"] =
      List.replicate 4 (.refused (some .onlyStringEnumNumberAllowed)) := by
  native_decide

/- **An Enumeration field side is refused here and admitted by the Kernel**, provided every literal
   is a valid stored token; a non-token literal draws
   `MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION_OR_CATEGORY`. The local refusal is
   `unsupportedFieldsFamily`, a representation limit rather than a Kernel gate, and it claims no
   class — so this row locks a **known** shortfall rather than asserting the Kernel refuses the
   shape. Closing it is a representation extension, not a projection fix. -/
example : pairAdmission "Choice" "Choice2" = .refused none := by native_decide

end A12Kernel.Conformance.ValueListQuantifierKindGate
