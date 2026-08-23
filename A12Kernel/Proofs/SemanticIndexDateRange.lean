import A12Kernel.Elaboration.SemanticIndexDateRange

/-! # Keyed DateRange operand laws

The keyed read is deliberately not a second component account. These laws pin the two properties that
make that true: it factors through the same shared component clause the direct read uses, and its two
failure classes stay separated — an unresolvable lookup propagates while a wrong-kind selected cell
collapses the way a direct malformed read does.
-/

namespace A12Kernel

/-- The keyed read factors into the range projection followed by the shared component clause, so
emptiness, unavailability, and fillability follow from that clause's own laws rather than being
restated for this route. Together with `resolveDateRangeBoundNumericOperand_factors` this is what
makes the keyed and direct reads structurally unable to disagree about a reached observation. -/
theorem semanticIndexDateRangeBoundPart_resolve_factors
    (operation : CheckedSemanticIndexDateRangeBoundPart model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (outer : Env) (observed : CellObservation DateRangeCellValue)
    (reached : operation.source.observePreliminaryRange preliminary keyRaw
      .validation outer = .ok observed) :
    operation.resolvePreliminaryNumericOperand preliminary keyRaw outer =
      .ok (operation.part.fromDateRangeBoundObservation operation.bound
        observed) := by
  simp [CheckedSemanticIndexDateRangeBoundPart.resolvePreliminaryNumericOperand,
    reached]

/-- A lookup that could not be resolved at all keeps its own error, because a consumer must be able
to tell an unresolvable column from a resolved one that selected nothing. -/
theorem semanticIndexDateRangeBoundPart_resolve_context
    (operation : CheckedSemanticIndexDateRangeBoundPart model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (outer : Env) (error : SemanticIndexContextError)
    (failed : operation.source.observePreliminaryRange preliminary keyRaw
      .validation outer = .error (.context error)) :
    operation.resolvePreliminaryNumericOperand preliminary keyRaw outer =
      .error error := by
  simp [CheckedSemanticIndexDateRangeBoundPart.resolvePreliminaryNumericOperand,
    failed]

/-- A selected cell whose kind is not a DateRange collapses to formal unavailability rather than to
an error or a zero. The static gate makes it unreachable; this keeps a malformed checked document
from acquiring a value through the keyed route when it could not through the direct one. -/
theorem semanticIndexDateRangeBoundPart_resolve_wrongKind
    (operation : CheckedSemanticIndexDateRangeBoundPart model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (outer : Env) (fault : DirectDateRangeFault)
    (failed : operation.source.observePreliminaryRange preliminary keyRaw
      .validation outer = .error (.payload fault)) :
    operation.resolvePreliminaryNumericOperand preliminary keyRaw outer =
      .ok (.unknown .malformed) := by
  simp [CheckedSemanticIndexDateRangeBoundPart.resolvePreliminaryNumericOperand,
    failed]

/-- The keyed source carries the shared semantic-index certificate unchanged, so widening the index
field's kind reaches this operand without a second admission rule. -/
theorem checkedDateRangeSemanticIndex_index_unconstrained
    (checked : CheckedDateRangeSemanticIndexSource model) :
    model.admitsSingleGroupDeclaration checked.group
        checked.indexDeclaration = true ∧
      (checked.group.indexField == some checked.indexDeclaration.id) = true :=
  ⟨checked.indexOwned, checked.indexDeclared⟩

/-- The certified component read carries its selected declaration's own exposure witness, so no
consumer can reach a component the declared profile does not expose. The witness is stated over the
certificate's retained profile, which is the same set the direct component gate re-derives from the
declaration. -/
theorem checkedSemanticIndexDateRangeBoundPart_exposed
    (operation : CheckedSemanticIndexDateRangeBoundPart model) :
    operation.part.admittedBy model.hasBaseYear
      operation.source.format.components = true :=
  operation.componentExposed

/-- The keyed source's retained profile is the model's own certified profile for that declaration, so
no consumer can compare or extract against a profile the model does not declare. -/
theorem checkedDateRangeSemanticIndex_profile_owned
    (checked : CheckedDateRangeSemanticIndexSource model) :
    model.dateRangeSourceProfile checked.target =
      some (checked.targetDeclaration, checked.policy, checked.format) :=
  checked.targetAdmitted

/-- Stored equality reads each operand once and takes the direct carrier's own verdict over the two
retained identities in authored order, so the keyed pairing cannot describe a second equality. -/
theorem semanticIndexDateRangeEquality_evaluate_verdict
    (operation : CheckedSemanticIndexDateRangeEquality model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (environment : Env) (keyed direct : CellObservation DateRangeCellValue)
    (keyedRead : operation.keyed.observePreliminaryRange preliminary keyRaw
      .validation environment = .ok keyed)
    (directRead : operation.direct.evaluateAt environment .validation
      preliminary.base = .ok direct) :
    (operation.evaluate preliminary keyRaw environment).map (·.verdict) =
      .ok (operation.comparison.evalDateRangeCellValues
        (if operation.keyedFirst then keyed else direct).asValidationSimpleOperand
        (if operation.keyedFirst then direct else keyed).asValidationSimpleOperand) := by
  simp [CheckedSemanticIndexDateRangeEquality.evaluate, keyedRead, directRead,
    Except.map, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The authored order is retained rather than normalized: swapping the flag swaps which observation
each side of the verdict receives. An Explain consumer therefore recovers the authored shape. -/
theorem semanticIndexDateRangeEquality_order_retained
    (operation : CheckedSemanticIndexDateRangeEquality model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (environment : Env) (keyed direct : CellObservation DateRangeCellValue)
    (keyedRead : operation.keyed.observePreliminaryRange preliminary keyRaw
      .validation environment = .ok keyed)
    (directRead : operation.direct.evaluateAt environment .validation
      preliminary.base = .ok direct) :
    (operation.evaluate preliminary keyRaw environment).map
        (fun result => (result.left, result.right)) =
      .ok (if operation.keyedFirst then (keyed, direct) else (direct, keyed)) := by
  simp [CheckedSemanticIndexDateRangeEquality.evaluate, keyedRead, directRead,
    Except.map, Except.mapError, bind, Except.bind, pure, Except.pure]
  split <;> simp

/-- The two direct endpoint owners gate on complementary conditions, so one retained profile falls
into exactly one runtime domain under one model. This is the claim that licenses reading the keyed
endpoint's domain off its certificate instead of off which owner certified the operand. -/
theorem dateRangeSemanticIndex_domain_total (format : DateRangeInputFormat)
    (baseYear : Option Int) :
    format.supportsDirectBound baseYear = true ↔
      ¬ (format.includesYear = false ∧ baseYear = none) := by
  cases format <;> cases baseYear <;>
    simp [DateRangeInputFormat.supportsDirectBound,
      DateRangeInputFormat.includesYear]

/-- A keyed endpoint whose profile resolves to Dates never compares against a bare label. The static
gate does not establish this, so it fails closed rather than manufacturing a domain. -/
theorem semanticIndexDateRangeBoundComparison_exactAgainstYearless
    (operation : CheckedSemanticIndexDateRangeBoundComparison model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (environment : Env) (direct : CheckedYearlessDateRangeBound model)
    (isYearless : operation.direct = .yearless direct)
    (isExact : operation.keyed.exactDomain = true)
    (range : CellObservation DateRangeCellValue)
    (reached : operation.keyed.observePreliminaryRange preliminary keyRaw
      .validation environment = .ok range) :
    operation.evaluate preliminary keyRaw environment =
      .error (.endpoint .mixedDomains) := by
  simp [CheckedSemanticIndexDateRangeBoundComparison.evaluate, reached,
    isYearless, isExact, Except.mapError, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw]

/-- And the other direction: a bare-label profile never acquires a resolved comparison from a direct
operand its own model could complete. -/
theorem semanticIndexDateRangeBoundComparison_yearlessAgainstExact
    (operation : CheckedSemanticIndexDateRangeBoundComparison model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (environment : Env) (direct : CheckedDateRangeBound model)
    (isExact : operation.direct = .exact direct)
    (isYearless : operation.keyed.exactDomain = false)
    (range : CellObservation DateRangeCellValue)
    (reached : operation.keyed.observePreliminaryRange preliminary keyRaw
      .validation environment = .ok range) :
    operation.evaluate preliminary keyRaw environment =
      .error (.endpoint .mixedDomains) := by
  simp [CheckedSemanticIndexDateRangeBoundComparison.evaluate, reached,
    isExact, isYearless, Except.mapError, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw]

/-- The certified pair retains its comparability witness, so no consumer can compare two endpoint
profiles the ordinary direct temporal rule refuses. -/
theorem semanticIndexDateRangeBoundComparison_admitted
    (operation : CheckedSemanticIndexDateRangeBoundComparison model) :
    operation.comparison.admitsFormats model.baseYear.isSome
      operation.keyed.format.components operation.direct.components = true :=
  operation.formatsAdmitted

end A12Kernel
