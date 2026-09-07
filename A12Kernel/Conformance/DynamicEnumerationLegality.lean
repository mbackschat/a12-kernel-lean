import A12Kernel.Elaboration.DynamicEnumerationLegality
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Elaboration.UnraisedDiagnostic

/-! # Locks on dynamic-enumeration legality

Each case fixes one reading a consumer would otherwise adopt: that a String field is simply admissible, that a length bound is unrelated to a value list, that the stages report independently, or that the code identifies its cause.

The catalog keys are the exact codes the `dynamicEnumerations` probe route surfaced, each drawn by a single witness rule in a model carrying no other rule, so the attribution is the rule rather than the model ([checkpoint](../../docs/SOURCES.md#src-dynamic-enumeration-legality)).
-/

namespace A12Kernel.Conformance.DynamicEnumerationLegality

open A12Kernel

/-- The measured accepted control: a plain String target, canonical gate, nothing else declared.
The derivation extracted this rule's constant, which is why acceptance is a load-bearing case and
not merely the absence of a refusal. -/
private def acceptedControl : DynEnumCandidate :=
  { target := .string {} }

/- Acceptance, and the equivalence a consumer may decide from either side. -/
example :
    dynEnumLegality acceptedControl = none ∧ dynEnumViolations acceptedControl = [] := by
  native_decide

/- The violation list is the pipeline's audit trail: it names every stage condition the candidate
   breaks, in stage order, where the pipeline reports only the first. A consumer offering "all the
   problems with this rule" has to read this one, and its tail must not be silently short. -/
example :
    dynEnumViolations
        { target := .number { maxFractionalDigits := 2 },
          usesRepetitionNotUnique := true,
          gateCanonical := false,
          valueCalculation := some .calcOpForm } =
      [.targetType, .repetitionNotUnique, .gateForm, .calcOpForm] ∧
      dynEnumViolations { target := .string {}, gateCanonical := false } = [.gateForm] := by
  native_decide

/- An earlier stage completely hides a later one. This candidate is broken at three stages at once
   and reports the first; a consumer collecting "all the problems with this rule" from one call gets
   exactly one, and it is not the one it would guess from reading the condition. -/
example :
    dynEnumLegality
        { target := .number { maxFractionalDigits := 2 },
          usesRepetitionNotUnique := true,
          gateCanonical := false,
          valueCalculation := some .calcOpForm } =
      some .targetType := by
  native_decide

/- The model's world is tested before the target's declared type, so a non-A12 model reports its
   world even when the target would also have been refused. This arm is modelled from the Kernel's
   own guard and carries no witness through the probe route, which is why the pipeline states it
   unconditionally rather than leaving it to a reachability judgement. -/
example :
    dynEnumLegality { hModel := true, target := .otherKind } = some .hModel ∧
      dynEnumLegality { hModel := false, target := .otherKind } = some .targetType := by
  native_decide

/- The stages are ordered, not independent: the same candidate with only the type repaired moves to
   the next violated stage rather than being accepted. -/
example :
    dynEnumLegality
        { target := .number {},
          usesRepetitionNotUnique := true,
          gateCanonical := false,
          valueCalculation := some .calcOpForm } =
      some .repetitionNotUnique ∧
      dynEnumLegality
        { target := .number {},
          gateCanonical := false,
          valueCalculation := some .calcOpForm } =
      some .gateForm ∧
      dynEnumLegality
        { target := .number {},
          valueCalculation := some .calcOpForm } =
      some .calcOpForm := by
  native_decide

/- A String target is admissible only with nothing declared. Each of the four constraints refuses on
   its own, which is the grid a reimplementer most often gets wrong by admitting a length bound. -/
example :
    targetTypeAdmits (.string {}) = true ∧
      targetTypeAdmits (.string { maxLength := 10 }) = false ∧
      targetTypeAdmits (.string { minLength := 1 }) = false ∧
      targetTypeAdmits (.string { pattern := "[A-Z]+" }) = false ∧
      targetTypeAdmits (.string { noValueValidation := true }) = false := by
  native_decide

/- The two length bounds are tested differently, so their absent encodings differ: a declared
   maximum of `0` is the absent maximum and admits, while a declared minimum of `0` is a real
   constraint and refuses. A consumer normalising both to `0` loses this. -/
example :
    targetTypeAdmits (.string { maxLength := 0 }) = true ∧
      targetTypeAdmits (.string { maxLength := -1 }) = true ∧
      targetTypeAdmits (.string { minLength := 0 }) = false ∧
      targetTypeAdmits (.string { minLength := -1 }) = true := by
  native_decide

/- The empty pattern is the absent pattern: emptiness is the test, not nullity. -/
example :
    targetTypeAdmits (.string { pattern := "" }) = true ∧
      targetTypeAdmits (.string { pattern := " " }) = false := by
  native_decide

/- An extensible enum is a String declaration and has no branch of its own, so it is refused even
   though a plain Enumeration is admitted unconditionally. This is the trap: the two look like the
   same kind of thing to an author and are not the same kind of thing here. -/
example :
    targetTypeAdmits (.string { extensibleEnum := true }) = false ∧
      targetTypeAdmits (.string { extensibleEnum := true, maxLength := 0, minLength := -1 }) =
        false ∧
      targetTypeAdmits .enumeration = true := by
  native_decide

/- A Number is admissible only unconstrained, and each constraint refuses on its own. Zero
   fractional digits is the admitted case, so the discriminator is `> 0` and not "declared". -/
example :
    targetTypeAdmits (.number {}) = true ∧
      targetTypeAdmits (.number { maxFractionalDigits := 0 }) = true ∧
      targetTypeAdmits (.number { maxFractionalDigits := 2 }) = false ∧
      targetTypeAdmits (.number { minFractionalDigits := 1 }) = false ∧
      targetTypeAdmits (.number { leadingZerosAllowed := true }) = false ∧
      targetTypeAdmits (.number { hasMaxValue := true }) = false ∧
      targetTypeAdmits (.number { hasMinValue := true }) = false := by
  native_decide

/- Both fractional-digit bounds are tested with `> 0` rather than "declared", so the Kernel's
   undeclared encoding is admitted alongside a literal zero. A consumer narrowing the test to
   equality with zero refuses a field the Kernel accepts, and no fixture spelled `0` can show it. -/
example :
    targetTypeAdmits (.number { maxFractionalDigits := -1 }) = true ∧
      targetTypeAdmits (.number { minFractionalDigits := -1 }) = true ∧
      targetTypeAdmits (.number { maxFractionalDigits := -1, minFractionalDigits := -1 }) = true ∧
      targetTypeAdmits (.number { maxFractionalDigits := 1 }) = false := by
  native_decide

/- A rule whose error entity is a group, or a field of any other kind, is refused by the same class
   as a badly constrained field — so the code does not tell a consumer that a field was involved. -/
example :
    targetTypeAdmits .group = false ∧ targetTypeAdmits .otherKind = false ∧
      dynEnumLegality { target := .group } = some .targetType ∧
      dynEnumLegality { target := .otherKind } = some .targetType := by
  native_decide

/- The target reference's cascade is ordered, and its last two arms collapse onto one code: a
   semantic index and a disagreeing iteration depth are indistinguishable to a consumer reading the
   code, though they are different candidates. A repair tool inverting the code will be wrong on
   one of them. -/
example :
    targetReferenceRefusal { hasSemanticIndex := true } = some .targetIteration ∧
      targetReferenceRefusal { indicesMatchGate := false } = some .targetIteration ∧
      ({ hasSemanticIndex := true } : DynEnumTargetReference) ≠
        { indicesMatchGate := false } := by
  native_decide

/- Order inside that cascade is observable too: a reference that is the wrong field *and* reaches
   through a category reports the wrong field, because that test is first. -/
example :
    targetReferenceRefusal { matchesGateField := false, hasCategoryAccess := true } =
        some .wrongTargetField ∧
      targetReferenceRefusal { hasCategoryAccess := true } = some .targetCategoryAccess ∧
      targetReferenceRefusal {} = none := by
  native_decide

/- Every catalog key is distinct and the vocabulary is closed at twelve, so a consumer switching on
   the code alone keeps the classes apart and has no residual case. -/
example :
    DynEnumRefusal.all.length = 12 ∧
      (DynEnumRefusal.all.map (·.catalogKey)).eraseDups.length = 12 := by
  native_decide

/- Eleven of the twelve are measured against the real Kernel, each by its own witness rule. The
   twelfth is `hModel`, whose branch a non-A12 model reaches and no witness through this route does.
   The list is written out rather than derived so that adding a class without measuring it breaks
   this case. -/
example :
    DynEnumRefusal.all.filter (· != .hModel) =
      [.targetType, .targetIsIndexField, .parallelIteration, .repetitionNotUnique, .gateForm,
       .wrongTargetField, .targetCategoryAccess, .targetIteration,
       .calcOpForm, .calcOpComparison, .unguardedOperand] := by
  native_decide

/- The keys the probe route surfaced, in the measured spelling. Two of the twelve break the
   `MVK_DYNENUM_` prefix their siblings share, which is the kind of near-miss a consumer building
   the key by concatenation would get wrong. -/
example :
    DynEnumRefusal.targetIteration.catalogKey = "MVK_INVALID_ITERATION" ∧
      DynEnumRefusal.wrongTargetField.catalogKey = "MVK_ERROR_WRONG_DYNENUM_FIELD" ∧
      DynEnumRefusal.targetCategoryAccess.catalogKey =
        "MVK_ERROR_DYNENUM_FIELD_WITH_CATEGORY" ∧
      (DynEnumRefusal.all.filter fun r =>
          r.catalogKey.startsWith "MVK_DYNENUM_").length = 9 := by
  native_decide

/- This vocabulary is disjoint from the reported static-diagnostic and never-reported vocabularies,
   so a consumer switching over all three keeps them apart. The load-bearing pair is
   `MVK_INVALID_ITERATION` against the consistency gate's `MVK_INVALID_ITERATION_IN_FILTER_CONDITION`:
   one is a prefix of the other, and they arrive from different services on different questions, so a
   consumer matching by prefix conflates a dyn-enum refusal with a parser one. -/
example :
    DynEnumRefusal.all.all (fun d =>
        KernelStaticDiagnostic.all.all (·.kernelCode != d.catalogKey) &&
          A12Kernel.UnraisedDiagnostic.all.all (·.catalogKey != d.catalogKey)) = true ∧
      DynEnumRefusal.targetIteration.catalogKey ≠
        KernelStaticDiagnostic.invalidIterationInFilterCondition.kernelCode ∧
      KernelStaticDiagnostic.invalidIterationInFilterCondition.kernelCode.startsWith
        DynEnumRefusal.targetIteration.catalogKey = true := by
  native_decide

/- The stage partition is exactly the value-calculation subvocabulary: those six classes and no
   others carry the last stage, so a consumer seeing one of them may conclude every earlier stage
   passed. -/
example :
    DynEnumValueCalcRefusal.all.map (·.toRefusal) =
        DynEnumRefusal.all.filter (·.stage == .valueCalculation) ∧
      DynEnumValueCalcRefusal.all.length = 6 := by
  native_decide

/- The whole stage partition, class by class in vocabulary order. All four stages are populated and
   the three-two-one-six shape is what makes "earliest violated stage" a total answer rather than a
   tie; moving any single class across a boundary breaks this line. -/
example :
    DynEnumRefusal.all.map (·.stage.order) = [0, 0, 0, 1, 1, 2, 3, 3, 3, 3, 3, 3] ∧
      (DynEnumRefusal.all.map (·.stage.order)).eraseDups = [0, 1, 2, 3] := by
  native_decide

end A12Kernel.Conformance.DynamicEnumerationLegality
