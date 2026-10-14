import A12Kernel.Semantics.HavingFieldValueList
import A12Kernel.Elaboration.Correlation
import A12Kernel.Semantics.ScalarEquality

namespace A12Kernel.Conformance.CorrelatedComparisonInputs
open A12Kernel

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def textPair : FlatComparison := .textFields .equal (.string { id := 1 }) (.string { id := 1 })
private def text (value : String) : CheckedCell := formalCheck { kind := .string } (.parsed (.str value))
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def emptyRequired : CheckedCell := { rawPresent := true, parsed := none, findings := [.required] }

private def validation {α : Type} (holds : α → α → Bool)
    (left : Except String (SimpleComparisonOperand α))
    (right : Unit → Except String (SimpleComparisonOperand α)) : Except String Verdict := do
  let left ← left
  let right ← right ()
  pure (evalSymmetricComparison holds left right)

example : textPair.foldSimpleReads .validation (fun _ => .ok (text "candidate"))
    (fun _ => .ok (text "captured")) validation = some (.ok .notFired) := by native_decide

example : textPair.foldSimpleReads .computation (fun _ => .ok invalid)
    (fun _ => .error "unbound captured row") evalComputationComparisonExcept =
      some (Except.ok (ε := String) (.poison .malformed)) ∧
    textPair.foldSimpleReads .validation (fun _ => .ok invalid)
    (fun _ => .error "unbound captured row") validation = some (.error "unbound captured row") := by native_decide

example : textPair.foldSimpleReads .computation (fun _ => .ok emptyRequired)
    (fun _ => .ok (text "present")) evalComputationComparisonExcept =
      some (Except.ok (ε := String) .notTrue) ∧
    textPair.foldSimpleReads .validation (fun _ => .ok emptyRequired)
    (fun _ => .ok (text "present")) validation = some (.ok .unknown) := by native_decide

example : textPair.foldSimpleReads .computation (fun _ => .ok emptyRequired)
    (fun _ => .ok invalid) evalComputationComparisonExcept =
      some (Except.ok (ε := String) (.poison .malformed)) := by native_decide

private def pair : CorrelatedHaving := .leaf (.simpleComparison .inner .outer textPair)
private def frame : CorrelationFrame := { innerEnv := [(0, 1)], outerEnv := [(0, 2)] }
private def context : CorrelationContext := {
  read := fun env _ => text (if env == frame.innerEnv then "candidate" else "captured") }

example : pair.evalTruthIn context frame = .fls ∧
    pair.evalComputationIn context frame = .ok .notTrue ∧
    pair.fieldIds = [1] ∧ pair.markedFieldIds = [1] := by native_decide

private def model : FlatModel := {
  fields := [{
    id := 1, groupPath := ["Form", "Rows"], name := "Tag",
    policy := { kind := .string }, repeatableScope := [10] }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

example : pair.wellFormedForEnvironments model [10] [10] = true ∧
    pair.wellFormedForEnvironments model [10] [] = false ∧
    pair.wellFormedForEnvironments model [] [10] = false ∧
    pair.reachesReopenedLevel model [10] = true ∧
    pair.reachesReopenedLevel model [20] = false := by native_decide

example : CorrelatedHaving.wellFormedForEnvironments (.leaf (.simpleComparison .inner .outer
    (.booleanFields .equal (.boolean { id := 1 }) (.boolean { id := 1 }))))
      model [10] [10] = false := by native_decide

private def clockComponents : TemporalComponents := {
  year := false, month := false, day := false, hour := true, minute := true, second := true }
private def clockField : FlatTemporalField := { id := 1, kind := .dateTime, components := clockComponents }
private def clockCell (instant : Int) : CheckedCell := {
  rawPresent := true, findings := []
  parsed := some (.temporal (.time { epochMillis := instant }
    ((TimeOfDay.ofHms? 12 30 0).get (by native_decide)))) }
private def clockPair : FlatComparison := .time .equal clockField clockField

example : clockPair.foldSimpleReads .validation (fun _ => .ok (clockCell 0))
    (fun _ => .ok (clockCell 86400000)) validation = some (.ok (.fired .value)) ∧
    clockPair.foldSimpleReads .computation (fun _ => .ok emptyRequired)
    (fun _ => .ok (clockCell 0)) evalComputationComparisonExcept =
      some (Except.ok (ε := String) .notTrue) ∧
    clockPair.foldSimpleReads .validation (fun _ => .ok emptyRequired)
    (fun _ => .ok (clockCell 0)) validation = some (.ok .unknown) := by native_decide

example : clockPair.foldSimpleReads .computation (fun _ => .ok invalid)
    (fun _ => .error "missing captured date") evalComputationComparisonExcept =
      some (Except.ok (ε := String) (.poison .malformed)) := by native_decide

private def rangeCell (finish : Nat) : CheckedCell := {
  rawPresent := true, findings := [], parsed := some (.dateRange (.yearlessMonth 1 finish)) }
private def rangePair : FlatComparison := .dateRange .equal { id := 1 } { id := 1 }

example : rangePair.foldSimpleReads .validation (fun _ => .ok (rangeCell 2))
    (fun _ => .ok (rangeCell 3)) validation = some (.ok .notFired) ∧
    rangePair.foldSimpleReads .computation (fun _ => .ok invalid)
    (fun _ => .error "missing captured range") evalComputationComparisonExcept =
      some (Except.ok (ε := String) (.poison .malformed)) ∧
    rangePair.foldSimpleReads .validation (fun _ => .ok invalid)
    (fun _ => .error "missing captured range") validation = some (.error "missing captured range") := by native_decide

private def partialModel : FlatModel := { model with fields := [{
  id := 1, groupPath := ["Form", "Rows"], name := "Tag", repeatableScope := [10]
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } }] }
private def dateField : FlatTemporalField := { id := 1, kind := .date, components := TemporalComponents.fullDate }

example : partialModel.admitsHavingSimpleComparison [10] [10]
    (.temporal .equal (.fieldValue dateField) (.fieldValue dateField)) = false ∧
    (CorrelationElabError.dateRangeComponentsMismatch ["Left"] ["Right"]).diagnostic? =
      some .invalidCompareToDateRange := by native_decide

private def fill (operator : FieldFillQuantifier) : CorrelatedHavingLeaf :=
  .fieldFill operator [.direct { origin := .inner, field := 1 }, .direct { origin := .outer, field := 1 }]
private def fillContext : CorrelationContext := {
  read := fun env _ => if env == frame.innerEnv then text "filled" else emptyRequired }

example : (fill .allFieldsFilled).evalTruthIn fillContext frame = .unknown ∧
    (fill .atLeastOneFieldFilled).evalTruthIn fillContext frame = .tru ∧
    (fill .moreThanOneFieldFilled).evalComputationIn fillContext frame = .ok .notTrue ∧
    CorrelatedHaving.fieldIds (.leaf (fill .allFieldsFilled)) = [1] ∧
    CorrelatedHaving.markedFieldIds (.leaf (fill .allFieldsFilled)) = [1] := by native_decide

private def failingFillContext : ResolvingCorrelationContext String := {
  stringExpressionUnavailable := "String expression unavailable"
  unsupportedDateCalendar := "calendar"
  temporalValueFailure := "value failure"
  worldUnavailable := "world unavailable"
  storedTextUnavailable := fun _ => "stored text unavailable"
  typeValidityValueFailure := "type validity value failure", groupUnavailable := fun _ => "group unavailable"
  bindingError := fun _ => "binding"
  read := fun env _ => if env == frame.innerEnv then .ok (text "filled") else .error "captured read" }

example : (fill .atLeastOneFieldFilled).evalComputationInResolving failingFillContext frame = .ok .holds ∧
    (fill .noFieldFilled).evalComputationInResolving failingFillContext frame = .ok .notTrue ∧
    (fill .atLeastOneFieldFilled).evalTruthInResolving failingFillContext frame = .error "captured read" ∧
    (fill .fieldsNotCollectivelyFilled).evalComputationInResolving failingFillContext frame = .error "captured read" := by native_decide

example : (fill .allFieldsFilled).wellFormedForEnvironments model [10] [10] = true ∧
    (fill .allFieldsFilled).wellFormedForEnvironments model [10] [] = false ∧
    (CorrelatedHavingLeaf.fieldFill .allFieldsFilled [.direct { origin := .inner, field := 1 },
      .direct { origin := .inner, field := 1 }]).wellFormedForEnvironments model [10] [10] = false ∧
    (CorrelationElabError.fieldFill .tooFewFields).diagnostic? = some .paramSizeInvalidN ∧
    (CorrelationElabError.fieldFill (.duplicateOperand 1)).diagnostic? = some .duplicateParam1 := by native_decide

private def membership (origin : HavingOrigin) (operator : ValueListMembershipOp) : CorrelatedHavingLeaf :=
  .literalMembership origin operator (.token (.string { id := 1 }) ["filled"])

example : (membership .inner .included).evalTruthIn fillContext frame = .tru ∧
    (membership .outer .included).evalTruthIn fillContext frame = .fls ∧
    (membership .outer .notIncluded).evalComputationIn fillContext frame = .ok .notTrue ∧
    (membership .outer .included).evalTruthInResolving failingFillContext frame = .error "captured read" ∧
    (membership .outer .notIncluded).evalComputationInResolving failingFillContext frame = .error "captured read" ∧
    CorrelatedHaving.markedFieldIds (.leaf (membership .outer .included)) = [1] ∧
    CorrelatedHaving.fieldIds (.leaf (membership .outer .included)) = [1] := by native_decide

example : (membership .inner .included).wellFormedForEnvironments model [10] [] = true ∧
    (membership .outer .included).wellFormedForEnvironments model [10] [] = false ∧
    (membership .outer .included).wellFormedForEnvironments model [] [10] = true ∧
    (CorrelatedHavingLeaf.literalMembership .inner .included (.token (.string { id := 1 }) [])).wellFormedForEnvironments model [10] [] = false := by native_decide

private def numericMembership : FlatLiteralMembership :=
  .number { id := 1, info := { scale := 0, signed := true } } [0]
private def cleanEmpty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }

example : numericMembership.evalValidation .included cleanEmpty = .notFired ∧
    numericMembership.evalComputation .included cleanEmpty = .notTrue ∧
    numericMembership.evalValidation .notIncluded invalid = .notFired ∧
    numericMembership.evalComputation .notIncluded invalid = .poison .malformed := by native_decide

private def fieldMembership : HavingFieldValueList := .token
  [.direct { origin := .inner, operand := .string { id := 1 } }]
  [.direct { origin := .outer, operand := .string { id := 1 } }]

private def membershipContext (read : HavingOrigin → FieldId → Except String CheckedCell) :
    ResolvingCorrelationContext String :=
  { failingFillContext with read := fun env => read (if env == frame.outerEnv then .outer else .inner) }

private def membershipOperators : List ComputationValueListOperator :=
  [.scalar .included, .scalar .notIncluded, .quantified .atLeastOne, .quantified .no, .quantified .notAll]

example : membershipOperators.map (fun op => fieldMembership.evalComputationRead op
      (membershipContext (fun _ _ => Except.ok (ε := String) (text "match"))) frame) =
    [.ok .holds, .ok .notTrue, .ok .holds, .ok .notTrue, .ok .notTrue] := by native_decide

example : membershipOperators.map (fun op => fieldMembership.evalComputationRead op
      (membershipContext (fun origin _ => if origin == .inner then .ok cleanEmpty else Except.error "members")) frame) =
    [.error "members", .error "members", .error "members", .error "members", .ok .notTrue] := by native_decide

example : membershipOperators.map (fun op => fieldMembership.evalComputationRead op
      (membershipContext (fun origin _ => if origin == .outer then .ok cleanEmpty else Except.error "subject")) frame) =
    [.error "subject", .error "subject", .ok .notTrue, .error "subject", .error "subject"] := by native_decide

example : membershipOperators.map (fun op => fieldMembership.evalValidationRead op
      (membershipContext (fun _ _ => Except.ok (ε := String) (text "match"))) frame) =
    [.ok (.fired .value), .ok .notFired, .ok (.fired .value), .ok .notFired, .ok .notFired] ∧
    fieldMembership.references = [{ origin := .inner, field := 1 }, { origin := .outer, field := 1 }] := by native_decide

private def fieldMembershipLeaf : CorrelatedHavingLeaf := .fieldMembership (.scalar .included) fieldMembership

example : fieldMembershipLeaf.evalTruthIn context frame = .fls ∧
    fieldMembershipLeaf.evalComputationIn context frame = .ok .notTrue ∧
    fieldMembershipLeaf.evalComputationInResolving failingFillContext frame = .error "captured read" ∧
    fieldMembershipLeaf.wellFormedForEnvironments model [10] [10] = true ∧
    fieldMembershipLeaf.wellFormedForEnvironments model [10] [] = false ∧
    CorrelatedHaving.markedFieldIds (.leaf fieldMembershipLeaf) = [1] := by native_decide

example : (HavingFieldValueList.token
      [.direct { origin := .inner, operand := .string { id := 1 } }]
      [.direct { origin := .inner, operand := .string { id := 1 } }]).wellFormedForEnvironments
        (.scalar .included) model [10] [10] = false ∧
    (HavingFieldValueList.token [] [.direct { origin := .inner, operand := .string { id := 1 } }]).wellFormedForEnvironments
        (.quantified .no) model [10] [10] = false := by native_decide

example : membershipOperators.map (fun op => fieldMembership.evalValidationRead op
      (membershipContext (fun origin _ => Except.error (if origin == .inner then "subject" else "members"))) frame) =
    [.error "members", .error "subject", .error "members", .error "members", .error "subject"] := by native_decide

example : membershipOperators.map (fun op => fieldMembership.evalComputationRead op
      (membershipContext (fun origin _ => Except.ok (ε := String) (if origin == .inner then emptyRequired else text "match"))) frame) =
    [.ok .notTrue, .ok .notTrue, .ok .notTrue, .ok .holds, .ok .notTrue] := by native_decide

private def membershipPrefix : HavingFieldValueList := .token
  [.direct { origin := .inner, operand := .string { id := 1 } }, .direct { origin := .inner, operand := .string { id := 2 } }]
  [.direct { origin := .outer, operand := .string { id := 1 } }]

example : [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
    membershipPrefix.evalComputationRead (.quantified operator)
      (membershipContext (fun _ field => if field == 2 then Except.error "late subject" else .ok (text "match"))) frame) =
    [.ok .holds, .ok .notTrue, .error "late subject"] := by native_decide

private def tokenLiteralList : HavingFieldValueList := .tokenLiterals
  [.direct { origin := .inner, operand := .string { id := 1 } }, .direct { origin := .outer, operand := .string { id := 1 } }]
  ["candidate"]

example : [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
    (CorrelatedHavingLeaf.fieldMembership (.quantified operator) tokenLiteralList).evalComputationIn context frame) =
      [.ok .holds, .ok .notTrue, .ok .holds] ∧
    tokenLiteralList.references = [{ origin := .inner, field := 1 }, { origin := .outer, field := 1 }] ∧
    CorrelatedHaving.markedFieldIds (.leaf (.fieldMembership (.quantified .notAll) tokenLiteralList)) = [1] := by native_decide

example : [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
    tokenLiteralList.evalComputationRead (.quantified operator)
      (membershipContext (fun origin _ => if origin == .inner then .ok (text "candidate") else Except.error "late subject")) frame) =
    [.ok .holds, .ok .notTrue, .error "late subject"] ∧
    [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
      tokenLiteralList.evalValidationRead (.quantified operator)
        (membershipContext (fun origin _ => if origin == .inner then .ok (text "candidate") else Except.error "late subject")) frame) =
    [.error "late subject", .error "late subject", .error "late subject"] := by native_decide

example : tokenLiteralList.wellFormedForEnvironments (.quantified .no) model [10] [10] = true ∧
    tokenLiteralList.wellFormedForEnvironments (.quantified .no) model [10] [] = false ∧
    tokenLiteralList.wellFormedForEnvironments (.scalar .included) model [10] [10] = false ∧
    (HavingFieldValueList.tokenLiterals [] ["candidate"]).wellFormedForEnvironments (.quantified .no) model [10] [10] = false ∧
    (HavingFieldValueList.tokenLiterals [.direct { origin := .inner, operand := .string { id := 1 } }] []).wellFormedForEnvironments
      (.quantified .no) model [10] [10] = false := by native_decide

example : [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
    tokenLiteralList.evalComputationRead (.quantified operator)
      (membershipContext (fun _ _ => Except.ok (ε := String) emptyRequired)) frame) =
    [.ok .notTrue, .ok .holds, .ok .notTrue] ∧
    [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
      tokenLiteralList.evalComputationRead (.quantified operator)
        (membershipContext (fun _ _ => Except.ok (ε := String) invalid)) frame) =
    [.ok (.poison .malformed), .ok (.poison .malformed), .ok (.poison .malformed)] := by native_decide

private def toleranceComparison (range : NumericToleranceRange) : NumericComparisonOf HavingNumericAtom := {
  op := .tolerance range
  left := .atom (.field { origin := .inner, field := { id := 1, info := { scale := 1, signed := true } } })
  right := .atom (.field { origin := .outer, field := { id := 1, info := { scale := 0, signed := true } } }) }

/-- A tolerance comparison carries no scale gate, so the enclosing text's suppression changes
nothing; rows `w01`, `w02` and `w05`, `w06` of the
[checkpoint](../../docs/sources/having-filter-probes.md#src-having-scale-warning-suppression). -/
example : [NumericToleranceRange.range1, .range2, .range5, .range10].all (fun range =>
    (toleranceComparison range).havingAdmitted (fun _ => true) &&
      ({ toleranceComparison range with suppressExactScaleWarning := true }).havingAdmitted (fun _ => true)) = true := by
  native_decide

private def toleranceRead : ResolvingCorrelationContext String := {
  read := fun env _ => if env == frame.innerEnv then .ok invalid else .error "captured read"
  stringExpressionUnavailable := "String expression unavailable"
  unsupportedDateCalendar := "calendar"
  temporalValueFailure := "value failure"
  worldUnavailable := "world unavailable"
  storedTextUnavailable := fun _ => "stored text unavailable"
  typeValidityValueFailure := "type validity value failure", groupUnavailable := fun _ => "group unavailable"
  bindingError := fun _ => "binding" }

example : (CorrelatedHavingLeaf.numeric (toleranceComparison .range1)).evalTruthInResolving toleranceRead frame =
      .error "captured read" ∧
    (CorrelatedHavingLeaf.numeric (toleranceComparison .range1)).evalComputationInResolving toleranceRead frame =
      .ok (.poison .malformed) ∧
    CorrelatedHaving.markedFieldIds (.leaf (.numeric (toleranceComparison .range1))) = [1] := by native_decide

private def lengthComparison : NumericComparisonOf HavingNumericAtom := {
  op := .ordinary .equal
  left := .atom (.stringLength .inner { id := 1 })
  right := .atom (.stringLength .outer { id := 1 }) }

-- The synthetic checked cell separates UTF-16 counting from prior legal-character admission (spec/06 §A).
example : (HavingNumericAtom.stringLength .inner { id := 1 }).readValidation
      { read := fun _ _ => { emptyRequired with findings := [] } } frame = .ok (.value 0 .growOnly) ∧
    (HavingNumericAtom.stringLength .inner { id := 1 }).readValidation
      { read := fun _ _ => emptyRequired } frame = .error () ∧
    (HavingNumericAtom.stringLength .inner { id := 1 }).readComputation
      { read := fun _ _ => emptyRequired } frame = .ok (.value 0) ∧
    (HavingNumericAtom.stringLength .inner { id := 1 }).readValidation
      { read := fun _ _ => { rawPresent := true, parsed := some (.str "😀"), findings := [] } } frame = .ok (.value 2 .fixed) := by native_decide

example : (CorrelatedHavingLeaf.numeric lengthComparison).evalTruthInResolving toleranceRead frame =
      .error "captured read" ∧
    (CorrelatedHavingLeaf.numeric lengthComparison).evalComputationInResolving toleranceRead frame =
      .ok (.poison .malformed) ∧
    CorrelatedHaving.markedFieldIds (.leaf (.numeric lengthComparison)) = [1] := by native_decide

private def projectedAtoms : List HavingNumericAtom := [
  .stringRange .inner { id := 1 } 1 2,
  .temporalPart .inner { id := 1, kind := .date, components := TemporalComponents.fullDate } (.date .year) ]

example : projectedAtoms.map (·.readValidation { read := fun _ _ => { emptyRequired with findings := [] } } frame) =
      [.ok (.value 0 .growOnly), .ok (.value 0 .both)] ∧
    projectedAtoms.map (·.readComputation { read := fun _ _ => emptyRequired } frame) =
      [.ok (.value 0), .ok (.value 0)] ∧
    projectedAtoms.map (·.readComputation { read := fun _ _ => invalid } frame) =
      [.ok (.poison .malformed), .ok (.poison .malformed)] := by native_decide

example : (HavingNumericAtom.stringRange .inner { id := 1 } 3 4).readValidation
      { read := fun _ _ => { rawPresent := true, parsed := some (.str "😀12"), findings := [] } } frame =
      .ok (.value 12 .fixed) ∧
    (HavingNumericAtom.stringRange .inner { id := 1 } 1 1).readValidation
      { read := fun _ _ => { rawPresent := true, parsed := some (.str "😀12"), findings := [] } } frame =
      .ok (.value 0 .fixed) := by native_decide

example : projectedAtoms.all (fun source =>
    let comparison : CorrelatedHavingLeaf := .numeric {
      op := .ordinary .equal
      left := .atom source
      right := .atom (.stringLength .outer { id := 1 }) }
    comparison.evalTruthInResolving toleranceRead frame == .error "captured read" &&
      comparison.evalComputationInResolving toleranceRead frame == .ok (.poison .malformed)) = true := by native_decide

private def conversionSource : ResolvedFieldValueAsNumberSource := { operand := .string { id := 1 }, scale := 0 }
private def conversionModel : FlatModel := { model with
  baseYear := some 2024
  fields := model.fields.map fun field => { field with
    stringPatternSource := some "[0-9]+", stringPolicy := { maxLength := some 15 } } }

private def conversionCondition (origin : HavingOrigin) (source : ResolvedFieldValueAsNumberSource) : CorrelatedHavingLeaf :=
  .numeric { op := .ordinary .equal, left := .atom (.fieldValueAsNumber origin source), right := .literal { value := 2, authoredScale := 0 } }

example : (conversionCondition .inner conversionSource).wellFormedForEnvironments conversionModel [10] [] = true ∧
    (conversionCondition .inner conversionSource).wellFormedForEnvironments model [10] [] = false ∧
    (conversionCondition .outer conversionSource).wellFormedForEnvironments conversionModel [10] [] = false ∧
    (conversionCondition .inner { conversionSource with scale := 1 }).wellFormedForEnvironments conversionModel [10] [] = false := by native_decide

example : (HavingNumericAtom.fieldValueAsNumber .inner conversionSource).readValidation
      { read := fun _ _ => { emptyRequired with findings := [] } } frame = .ok (.value 0 .both) ∧
    (HavingNumericAtom.fieldValueAsNumber .inner conversionSource).readComputation
      { read := fun _ _ => emptyRequired } frame = .ok (.value 0) ∧
    (conversionCondition .inner conversionSource).evalComputationInResolving toleranceRead frame =
      .ok (.poison .malformed) := by native_decide

example : (HavingNumericAtom.fieldValueAsNumber .inner conversionSource).readValidationResolving
      ({ toleranceRead with read := fun _ _ => .error "address" } : ResolvingCorrelationContext String) frame = .error "address" ∧
    (HavingNumericAtom.fieldValueAsNumber .inner conversionSource).readComputationResolving
      ({ toleranceRead with read := fun _ _ => .error "address" } : ResolvingCorrelationContext String) frame = .error "address" := by native_decide

private def conversionPair : CorrelatedHavingLeaf := .numeric {
  op := .ordinary .equal
  left := .atom (.fieldValueAsNumber .inner conversionSource)
  right := .atom (.fieldValueAsNumber .outer conversionSource) }

example : conversionPair.evalTruthInResolving toleranceRead frame = .error "captured read" ∧
    conversionPair.evalComputationInResolving toleranceRead frame = .ok (.poison .malformed) := by native_decide

private def configuredYearCondition (year : Int) : CorrelatedHaving :=
  .leaf (.numeric { op := .ordinary .equal, left := .atom (.baseYear year), right := .literal { value := 2024, authoredScale := 0 } })

example : (configuredYearCondition 2024).wellFormedForEnvironments conversionModel [] [] = true ∧
    (configuredYearCondition 2023).wellFormedForEnvironments conversionModel [] [] = false ∧
    (configuredYearCondition 2024).wellFormedForEnvironments model [] [] = false ∧
    (configuredYearCondition 2024).usesInner = false ∧
    (configuredYearCondition 2024).usesOuter = false ∧
    (configuredYearCondition 2024).fieldIds = [] := by native_decide

private def rangeNumeric (origin : HavingOrigin) (bound : DateRangeBound) (part : DateNumericPart) : HavingNumericAtom :=
  .dateRangeBoundPart origin { id := 1 } bound part

private def rangeNumericPair : CorrelatedHavingLeaf := .numeric {
  op := .ordinary .equal
  left := .atom (rangeNumeric .inner .start .month)
  right := .atom (rangeNumeric .outer .finish .month) }

example : (rangeNumeric .inner .start .month).readValidation { read := fun _ _ => rangeCell 8 } frame =
      .ok (.value 1 .fixed) ∧
    (rangeNumeric .inner .finish .month).readComputation { read := fun _ _ => rangeCell 8 } frame = .ok (.value 8) ∧
    (rangeNumeric .inner .start .month).readValidation
      { read := fun _ _ => { emptyRequired with findings := [] } } frame = .ok (.value 0 .both) ∧
    (rangeNumeric .inner .start .month).readComputation { read := fun _ _ => emptyRequired } frame = .ok (.value 0) ∧
    (rangeNumeric .inner .start .month).readValidation { read := fun _ _ => text "wrong kind" } frame = .error () := by native_decide

example : rangeNumericPair.evalTruthInResolving toleranceRead frame = .error "captured read" ∧
    rangeNumericPair.evalComputationInResolving toleranceRead frame = .ok (.poison .malformed) ∧
    (rangeNumeric .inner .start .month).readValidationResolving
      { toleranceRead with read := fun _ _ => .error "address" } frame = .error "address" ∧
    (rangeNumeric .inner .start .month).readComputationResolving
      { toleranceRead with read := fun _ _ => .error "address" } frame = .error "address" ∧
    CorrelatedHaving.fieldIds (.leaf rangeNumericPair) = [1] ∧
    CorrelatedHaving.markedFieldIds (.leaf rangeNumericPair) = [1] := by native_decide

private def rangeNumericModel : FlatModel := { model with fields := model.fields.map fun field =>
  { field with policy := { kind := .dateRange }, dateRangePolicy := some { format := "MM", separator := "/" } } }

private def rangeNumericLeaf (origin : HavingOrigin) (part : DateNumericPart) : CorrelatedHavingLeaf :=
  .numeric { op := .ordinary .equal, left := .atom (rangeNumeric origin .start part), right := .literal { value := 1, authoredScale := 0 } }

example : (rangeNumericLeaf .inner .month).wellFormedForEnvironments rangeNumericModel [10] [] = true ∧
    (rangeNumericLeaf .inner .day).wellFormedForEnvironments rangeNumericModel [10] [] = false ∧
    (rangeNumericLeaf .inner .year).wellFormedForEnvironments rangeNumericModel [10] [] = false ∧
    (rangeNumericLeaf .inner .year).wellFormedForEnvironments { rangeNumericModel with baseYear := some 2024 } [10] [] = true ∧
    (rangeNumericLeaf .inner .month).wellFormedForEnvironments model [10] [] = false ∧
    (rangeNumericLeaf .outer .month).wellFormedForEnvironments rangeNumericModel [10] [] = false := by native_decide

private def subdayRef (origin : HavingOrigin) : HavingTemporalRef := {
  origin, field := { id := 1, kind := .dateTime, components := TemporalComponents.ofFormat "yyyy-MM-dd'T'HH:mm:ss" } }
private def subdayAtom : HavingNumericAtom := .dateTimeDifference .hours (.fieldValue (subdayRef .inner)) (.fieldValue (subdayRef .outer))
private def subdayCondition : CorrelatedHaving := .leaf (.numeric {
  op := .ordinary .equal, left := .atom subdayAtom, right := .literal { value := 0, authoredScale := 0 } })

example : subdayCondition.fieldIds = [1] ∧ subdayCondition.markedFieldIds = [1] ∧
    subdayCondition.usesInner = true ∧ subdayCondition.usesOuter = true ∧
    subdayAtom.fieldOrigins = [(.inner, 1), (.outer, 1)] := by native_decide

example : subdayAtom.readValidationResolving toleranceRead frame = .error "captured read" ∧
    subdayAtom.readComputationResolving toleranceRead frame = .ok (.poison .malformed) ∧
    subdayAtom.readValidationResolving { toleranceRead with read := fun _ _ => .error "first read" } frame = .error "first read" ∧
    subdayAtom.readComputationResolving { toleranceRead with read := fun _ _ => .error "first read" } frame = .error "first read" := by native_decide

example : subdayAtom.readValidation { read := fun _ _ => { emptyRequired with findings := [] } } frame = .ok (.value 0 .both) ∧
    subdayAtom.readComputation { read := fun _ _ => emptyRequired } frame = .ok (.value 0) ∧
    subdayAtom.readValidation { read := fun _ _ => invalid } frame = .error () ∧
    subdayAtom.readComputation { read := fun _ _ => invalid } frame = .ok (.poison .malformed) := by native_decide

private def subdayModel : FlatModel := { model with fields := model.fields.map fun field => { field with
  policy := { kind := .temporal .dateTime (subdayRef .inner).field.components },
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } } }

example : subdayCondition.wellFormedForEnvironments subdayModel [10] [10] = true ∧
    subdayCondition.wellFormedForEnvironments subdayModel [10] [] = false ∧
    subdayCondition.wellFormedForEnvironments model [10] [10] = false ∧
    CorrelatedHaving.outerIterationScopes subdayModel subdayCondition = [none, some [10]] := by native_decide

private def aggregateRef (origin : HavingOrigin) (signed : Bool := true) : HavingNumberRef := {
  origin, field := { id := 1, info := { scale := 0, signed } } }
private def aggregateAtom (op : NumericAggregateOp) (signed : Bool := true) : HavingNumericAtom :=
  .aggregate op [.direct (aggregateRef .inner), .direct (aggregateRef .outer signed)]
private def aggregateRead : CorrelationContext := {
  read := fun env _ => if env == frame.innerEnv then
    { rawPresent := true, parsed := some (.num 2), findings := [] }
    else { emptyRequired with findings := [] } }

example : (aggregateAtom .sum).readValidation aggregateRead frame = .ok (.value 2 .both) ∧
    (aggregateAtom .sum false).readValidation aggregateRead frame = .ok (.value 2 .growOnly) ∧
    (aggregateAtom .minimum).readValidation aggregateRead frame = .ok (.value 2 .shrinkOnly) ∧
    (aggregateAtom .maximum).readValidation aggregateRead frame = .ok (.value 2 .growOnly) ∧
    (aggregateAtom .distinctCount).readValidation aggregateRead frame = .ok (.value 1 .growOnly) := by native_decide

private def aggregateStructuralRead : ResolvingCorrelationContext String := {
  stringExpressionUnavailable := "String expression unavailable"
  unsupportedDateCalendar := "calendar"
  temporalValueFailure := "value failure"
  worldUnavailable := "world unavailable"
  storedTextUnavailable := fun _ => "stored text unavailable"
  typeValidityValueFailure := "type validity value failure", groupUnavailable := fun _ => "group unavailable"
  bindingError := fun _ => "binding"
  read := fun env _ => if env == frame.innerEnv then
    .ok { emptyRequired with findings := [] }
    else .error "captured read" }

example : [NumericAggregateOp.sum, .minimum, .maximum, .distinctCount].all (fun op =>
    (aggregateAtom op).readValidationResolving toleranceRead frame == .ok (.error ()) &&
    (aggregateAtom op).readComputationResolving toleranceRead frame == .ok (.poison .malformed) &&
    (aggregateAtom op).readComputationResolving aggregateStructuralRead frame == .error "captured read") = true := by native_decide

private def aggregateModel : FlatModel := { model with fields := model.fields.map fun field =>
  { field with policy := { kind := .number { scale := 0, signed := true } } } }
private def aggregateCondition (first : HavingNumberRef) (rest : List HavingNumberRef) : CorrelatedHaving :=
  .leaf (.numeric { op := .ordinary .equal, left := .atom (.aggregate .sum ((first :: rest).map .direct)), right := .literal { value := 2, authoredScale := 0 } })

example : (aggregateCondition (aggregateRef .inner) [aggregateRef .outer]).wellFormedForEnvironments aggregateModel [10] [10] = true ∧
    (aggregateCondition (aggregateRef .inner) [aggregateRef .inner]).wellFormedForEnvironments aggregateModel [10] [10] = false ∧
    (aggregateCondition (aggregateRef .inner) []).wellFormedForEnvironments aggregateModel [10] [10] = false ∧
    (aggregateCondition (aggregateRef .inner) [aggregateRef .outer]).wellFormedForEnvironments aggregateModel [10] [] = false ∧
    (aggregateCondition (aggregateRef .inner) [aggregateRef .outer]).wellFormedForEnvironments model [10] [10] = false ∧
    (aggregateCondition (aggregateRef .inner) [aggregateRef .outer]).markedFieldIds = [1] := by native_decide

example : (HavingNumericAtom.aggregate .sum [.direct { origin := .inner, field := { id := 1, info := { scale := 2, signed := true } } },
      .direct (aggregateRef .outer)]).summary = .field 2 ∧
    (HavingNumericAtom.aggregate .distinctCount [.direct { origin := .inner, field := { id := 1, info := { scale := 2, signed := true } } },
      .direct (aggregateRef .outer)]).summary = .field 0 := by native_decide

example : [NumericAggregateOp.sum, .minimum, .maximum].all (fun op =>
    (HavingNumericAtom.aggregate op [.direct (aggregateRef .inner),
      .direct { origin := .outer, field := { id := 2, info := { scale := 2, signed := true } } }]).summary == .field 2) = true ∧
    (HavingNumericAtom.aggregate .distinctCount [.direct (aggregateRef .inner),
      .direct { origin := .outer, field := { id := 2, info := { scale := 2, signed := true } } }]).summary = .field 0 := by native_decide

private def clockSourcePair : FlatComparison := .temporal .before .nowValue (.fieldValue (subdayRef .outer).field)

example : clockSourcePair.evalSimpleValidationReads (fun _ => .error "unexpected") (fun _ => .error "field") =
    Except.error (α := Verdict) "field" ∧
    clockSourcePair.evalSimpleComputationReads (fun _ => .error "unexpected") (fun _ => .error "field") =
      Except.ok (ε := String) (.poison .malformed) ∧
    clockSourcePair.evalSimpleComputationReads (fun _ => .error "unexpected") (fun _ => .error "field")
      (some { now := { epochMillis := 0 } }) = Except.error (α := ComputationConditionResult) "field" := by native_decide

private def injectedCalendar : World := {
  now := { epochMillis := 0 }, modelZoneRules := {
    today? := fun _ _ => some { epochMillis := 1234 }
    resolveLocal? := fun _ _ _ _ _ _ _ => some { epochMillis := 1234 } } }

example : [FlatTemporalOperand.todayValue "UTC", .baseYearValue "UTC" 1970,
    .baseYearRangeValue "UTC" 1970 .start, .baseYearRangeValue "UTC" 1970 .finish].all (fun source =>
      let comparison := FlatComparison.temporal .equal source (.literalValue { epochMillis := 1234 })
      comparison.evalSimpleValidationReads (fun _ => Except.error "unexpected") (fun _ => Except.error "unexpected")
        (some injectedCalendar) == .ok (.fired .value) &&
      comparison.evalSimpleComputationReads (fun _ => Except.error "unexpected") (fun _ => Except.error "unexpected")
        (some injectedCalendar) == .ok .holds &&
      comparison.evalSimpleValidationReads (fun _ => Except.error "unexpected") (fun _ => Except.error "unexpected") ==
        .ok .unknown &&
      comparison.evalSimpleComputationReads (fun _ => Except.error "unexpected") (fun _ => Except.error "unexpected") ==
        .ok (.poison .malformed)) = true := by native_decide

example : ComputationCondition.evalSimpleComparison
    (.temporal .equal (.todayValue "UTC") (.literalValue { epochMillis := 1234 }))
    { read := fun _ => invalid, world := some injectedCalendar } = .holds := by native_decide

private def gapLiteral : FlatTemporalOperand := .localDateTimeValue .europeBerlin
  ((LocalDateTime.ofYmdHms? 2024 3 31 2 30 0).get (by native_decide))
private def stampField : FlatTemporalOperand := .fieldValue
  { id := 1, kind := .dateTime, components := TemporalComponents.now }
private def gapPair (literalFirst : Bool) : FlatComparison :=
  if literalFirst then .temporal .before gapLiteral stampField
  else .temporal .after stampField gapLiteral

example : [false, true].all (fun first => [invalid, emptyRequired].all fun cell =>
    (gapPair first).evalSimpleValidationReads (fun _ => .ok cell) (fun _ => .ok cell)
      none (some "value failure") == .error "value failure") = true := by native_decide

example : (gapPair false).evalSimpleComputationReads (fun _ => .ok invalid) (fun _ => .ok invalid)
      none (some "value failure") = .ok (.poison .malformed) ∧
    (gapPair true).evalSimpleComputationReads (fun _ => .ok invalid) (fun _ => .ok invalid)
      none (some "value failure") = .error "value failure" ∧
    (gapPair false).evalSimpleComputationReads (fun _ => .ok emptyRequired) (fun _ => .ok emptyRequired)
      none (some "value failure") = .error "value failure" := by native_decide

private def gapCondition : CorrelatedHaving := .leaf (.simpleComparison .inner .inner (gapPair true))
example : gapCondition.evalComputationIn { read := fun _ _ => emptyRequired } frame =
      .error .valueFailure ∧
    gapCondition.scanComputation { read := fun _ _ => emptyRequired } []
      (fun (n : Nat) _ => Sum.inl (β := Unit) (n + 1)) [] 0 = .ok (.exhausted 0) := by native_decide

end A12Kernel.Conformance.CorrelatedComparisonInputs
