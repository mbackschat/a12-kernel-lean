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
    pair.evalComputationIn context frame = .notTrue ∧
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
  .fieldFill operator [{ origin := .inner, field := 1 }, { origin := .outer, field := 1 }]
private def fillContext : CorrelationContext := {
  read := fun env _ => if env == frame.innerEnv then text "filled" else emptyRequired }

example : (fill .allFieldsFilled).evalTruthIn fillContext frame = .unknown ∧
    (fill .atLeastOneFieldFilled).evalTruthIn fillContext frame = .tru ∧
    (fill .moreThanOneFieldFilled).evalComputationIn fillContext frame = .notTrue ∧
    CorrelatedHaving.fieldIds (.leaf (fill .allFieldsFilled)) = [1] ∧
    CorrelatedHaving.markedFieldIds (.leaf (fill .allFieldsFilled)) = [1] := by native_decide

private def failingFillContext : ResolvingCorrelationContext String := {
  bindingError := fun _ => "binding"
  read := fun env _ => if env == frame.innerEnv then .ok (text "filled") else .error "captured read" }

example : (fill .atLeastOneFieldFilled).evalComputationInResolving failingFillContext frame = .ok .holds ∧
    (fill .noFieldFilled).evalComputationInResolving failingFillContext frame = .ok .notTrue ∧
    (fill .atLeastOneFieldFilled).evalTruthInResolving failingFillContext frame = .error "captured read" ∧
    (fill .fieldsNotCollectivelyFilled).evalComputationInResolving failingFillContext frame = .error "captured read" := by native_decide

example : (fill .allFieldsFilled).wellFormedForEnvironments model [10] [10] = true ∧
    (fill .allFieldsFilled).wellFormedForEnvironments model [10] [] = false ∧
    (CorrelatedHavingLeaf.fieldFill .allFieldsFilled [{ origin := .inner, field := 1 },
      { origin := .inner, field := 1 }]).wellFormedForEnvironments model [10] [10] = false ∧
    (CorrelationElabError.fieldFill .tooFewFields).diagnostic? = some .paramSizeInvalidN ∧
    (CorrelationElabError.fieldFill (.duplicateOperand 1)).diagnostic? = some .duplicateParam1 := by native_decide

private def membership (origin : HavingOrigin) (operator : ValueListMembershipOp) : CorrelatedHavingLeaf :=
  .literalMembership origin operator (.token (.string { id := 1 }) ["filled"])

example : (membership .inner .included).evalTruthIn fillContext frame = .tru ∧
    (membership .outer .included).evalTruthIn fillContext frame = .fls ∧
    (membership .outer .notIncluded).evalComputationIn fillContext frame = .notTrue ∧
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
  [{ origin := .inner, operand := .string { id := 1 } }]
  [{ origin := .outer, operand := .string { id := 1 } }]

private def membershipOperators : List ComputationValueListOperator :=
  [.scalar .included, .scalar .notIncluded, .quantified .atLeastOne, .quantified .no, .quantified .notAll]

example : membershipOperators.map (fun op => fieldMembership.evalComputationRead op
      (fun _ _ => Except.ok (ε := String) (text "match"))) =
    [.ok .holds, .ok .notTrue, .ok .holds, .ok .notTrue, .ok .notTrue] := by native_decide

example : membershipOperators.map (fun op => fieldMembership.evalComputationRead op
      (fun origin _ => if origin == .inner then .ok cleanEmpty else Except.error "members")) =
    [.error "members", .error "members", .error "members", .error "members", .ok .notTrue] := by native_decide

example : membershipOperators.map (fun op => fieldMembership.evalComputationRead op
      (fun origin _ => if origin == .outer then .ok cleanEmpty else Except.error "subject")) =
    [.error "subject", .error "subject", .ok .notTrue, .error "subject", .error "subject"] := by native_decide

example : membershipOperators.map (fun op => fieldMembership.evalValidationRead op
      (fun _ _ => Except.ok (ε := String) (text "match"))) =
    [.ok (.fired .value), .ok .notFired, .ok (.fired .value), .ok .notFired, .ok .notFired] ∧
    fieldMembership.references = [{ origin := .inner, field := 1 }, { origin := .outer, field := 1 }] := by native_decide

private def fieldMembershipLeaf : CorrelatedHavingLeaf := .fieldMembership (.scalar .included) fieldMembership

example : fieldMembershipLeaf.evalTruthIn context frame = .fls ∧
    fieldMembershipLeaf.evalComputationIn context frame = .notTrue ∧
    fieldMembershipLeaf.evalComputationInResolving failingFillContext frame = .error "captured read" ∧
    fieldMembershipLeaf.wellFormedForEnvironments model [10] [10] = true ∧
    fieldMembershipLeaf.wellFormedForEnvironments model [10] [] = false ∧
    CorrelatedHaving.markedFieldIds (.leaf fieldMembershipLeaf) = [1] := by native_decide

example : (HavingFieldValueList.token
      [{ origin := .inner, operand := .string { id := 1 } }]
      [{ origin := .inner, operand := .string { id := 1 } }]).wellFormedForEnvironments
        (.scalar .included) model [10] [10] = false ∧
    (HavingFieldValueList.token [] [{ origin := .inner, operand := .string { id := 1 } }]).wellFormedForEnvironments
        (.quantified .no) model [10] [10] = false := by native_decide

example : membershipOperators.map (fun op => fieldMembership.evalValidationRead op
      (fun origin _ => Except.error (if origin == .inner then "subject" else "members"))) =
    [.error "members", .error "subject", .error "members", .error "members", .error "subject"] := by native_decide

example : membershipOperators.map (fun op => fieldMembership.evalComputationRead op
      (fun origin _ => Except.ok (ε := String) (if origin == .inner then emptyRequired else text "match"))) =
    [.ok .notTrue, .ok .notTrue, .ok .notTrue, .ok .holds, .ok .notTrue] := by native_decide

private def membershipPrefix : HavingFieldValueList := .token
  [{ origin := .inner, operand := .string { id := 1 } }, { origin := .inner, operand := .string { id := 2 } }]
  [{ origin := .outer, operand := .string { id := 1 } }]

example : [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
    membershipPrefix.evalComputationRead (.quantified operator)
      (fun _ field => if field == 2 then Except.error "late subject" else .ok (text "match"))) =
    [.ok .holds, .ok .notTrue, .error "late subject"] := by native_decide

private def tokenLiteralList : HavingFieldValueList := .tokenLiterals
  [{ origin := .inner, operand := .string { id := 1 } }, { origin := .outer, operand := .string { id := 1 } }]
  ["candidate"]

example : [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
    (CorrelatedHavingLeaf.fieldMembership (.quantified operator) tokenLiteralList).evalComputationIn context frame) =
      [.holds, .notTrue, .holds] ∧
    tokenLiteralList.references = [{ origin := .inner, field := 1 }, { origin := .outer, field := 1 }] ∧
    CorrelatedHaving.markedFieldIds (.leaf (.fieldMembership (.quantified .notAll) tokenLiteralList)) = [1] := by native_decide

example : [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
    tokenLiteralList.evalComputationRead (.quantified operator)
      (fun origin _ => if origin == .inner then .ok (text "candidate") else Except.error "late subject")) =
    [.ok .holds, .ok .notTrue, .error "late subject"] ∧
    [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
      tokenLiteralList.evalValidationRead (.quantified operator)
        (fun origin _ => if origin == .inner then .ok (text "candidate") else Except.error "late subject")) =
    [.error "late subject", .error "late subject", .error "late subject"] := by native_decide

example : tokenLiteralList.wellFormedForEnvironments (.quantified .no) model [10] [10] = true ∧
    tokenLiteralList.wellFormedForEnvironments (.quantified .no) model [10] [] = false ∧
    tokenLiteralList.wellFormedForEnvironments (.scalar .included) model [10] [10] = false ∧
    (HavingFieldValueList.tokenLiterals [] ["candidate"]).wellFormedForEnvironments (.quantified .no) model [10] [10] = false ∧
    (HavingFieldValueList.tokenLiterals [{ origin := .inner, operand := .string { id := 1 } }] []).wellFormedForEnvironments
      (.quantified .no) model [10] [10] = false := by native_decide

example : [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
    tokenLiteralList.evalComputationRead (.quantified operator) (fun _ _ => Except.ok (ε := String) emptyRequired)) =
    [.ok .notTrue, .ok .holds, .ok .notTrue] ∧
    [ValueListQuantifier.atLeastOne, .no, .notAll].map (fun operator =>
      tokenLiteralList.evalComputationRead (.quantified operator) (fun _ _ => Except.ok (ε := String) invalid)) =
    [.ok (.poison .malformed), .ok (.poison .malformed), .ok (.poison .malformed)] := by native_decide

end A12Kernel.Conformance.CorrelatedComparisonInputs
