import A12Kernel.Conformance.NumericComputation.Support
import A12Kernel.Elaboration.NumericComputation.RunPlan

/-! # Checked Number computation-table locks -/

namespace A12Kernel.Conformance.NumericComputation.Table

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

private abbrev NumericRow := ComputationAlternative
  (CheckedNumericTargetComputationOperation model)

private def operation? (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedNumericTargetComputationOperation model) :=
  (elaborateNumericTargetComputationOperation
    model ["Root"] target expression).toOption

private def operationAt? (declaringGroup : GroupPath) (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedNumericTargetComputationOperation model) :=
  (elaborateNumericTargetComputationOperation
    model declaringGroup target expression).toOption

private def literalRow? (guard : ComputationCondition) (target : FieldId)
    (value : Rat) : Option NumericRow := do
  let operation ← operation? target
    (.literal { value, authoredScale := 0 })
  pure {
    precondition := guard
    operation := operation
  }

private def unguardedLiteralRow? (target : FieldId)
    (value : Rat) : Option NumericRow := do
  let operation ← operation? target
    (.literal { value, authoredScale := 0 })
  pure {
    precondition := none
    operation := operation
  }

private def literalRowAt? (declaringGroup : GroupPath)
    (guard : ComputationCondition) (target : FieldId)
    (value : Rat) : Option NumericRow := do
  let operation ← operationAt? declaringGroup target
    (.literal { value, authoredScale := 0 })
  pure {
    precondition := guard
    operation := operation
  }

private def divisionRow? (guard : ComputationCondition) : Option NumericRow := do
  let operation ←
    (elaborateNumericTargetComputationOperation model ["Root"] targetId
    (.binary .divide
      (.literal { value := 1, authoredScale := 0 })
      (.literal { value := 0, authoredScale := 0 }))
      (suppressExactScaleWarning := true)).toOption
  pure {
    precondition := guard
    operation := operation
  }

private def alteredPolicyRow? (guard : ComputationCondition) : Option NumericRow := do
  let operation ← operation? targetId
    (.literal { value := 3, authoredScale := 0 })
  let policy := { operation.policy with zeroAllowed := true }
  let alteredOperation : CheckedNumericTargetComputationOperation model := {
    operation := operation.operation
    policy
    targetMatches := operation.targetMatches }
  pure {
    precondition := guard
    operation := alteredOperation
  }

private def collectRows? : List (Option NumericRow) → Option (List NumericRow)
  | [] => some []
  | some row :: remaining => (row :: ·) <$> collectRows? remaining
  | none :: _ => none

private def tableError? (rows : List (Option NumericRow)) :
    Option NumericComputationTableError := do
  let alternatives ← collectRows? rows
  match certifyNumericComputationTable alternatives with
  | .error error => some error
  | .ok _ => none

private def tableOutcome? (rows : List (Option NumericRow))
    (input : ScalarComputationContext := context) :
    Option NumericTargetCheckResult := do
  let alternatives ← collectRows? rows
  let table ← (certifyNumericComputationTable alternatives).toOption
  (table.evaluate input).toOption

private def tableDeclaringGroups? (rows : List (Option NumericRow)) :
    Option (List GroupPath) := do
  let alternatives ← collectRows? rows
  let table ← (certifyNumericComputationTable alternatives).toOption
  pure table.declaringGroups

/- Construction rejects empty input and the first row that changes target or complete policy. -/
example :
    tableError? [] = some .empty ∧
    tableError? [
      literalRow? (.fieldNotFilled laterId) targetId 1,
      literalRow? (.fieldNotFilled laterId) sourceId 2] =
        some (.targetMismatch 2 targetId sourceId) ∧
    tableError? [
      literalRow? (.fieldNotFilled laterId) targetId 1,
      alteredPolicyRow? (.fieldNotFilled laterId)] =
        some (.targetPolicyMismatch 2) := by
  native_decide

/- Only a sole alternative may omit its precondition, and it selects directly without reading a guard field. -/
example :
    tableOutcome? [unguardedLiteralRow? targetId 3] =
      some (.supported (.accepted { unscaled := 3, scale := 0 })) ∧
    tableError? [unguardedLiteralRow? targetId 3,
      literalRow? (.fieldNotFilled laterId) targetId 4] =
        some (.unguardedAlternative 1) ∧
    tableError? [literalRow? (.fieldNotFilled laterId) targetId 3,
      unguardedLiteralRow? targetId 4] = some (.unguardedAlternative 2) := by
  native_decide

/- Same-target table assembly retains each row's definition placement even though target-owned runtime
evaluation does not consume it. -/
example :
    tableDeclaringGroups? [
      literalRow? (.fieldFilled sourceId) targetId 1,
      literalRowAt? ["Rules"] (.fieldNotFilled sourceId) targetId 2] =
      some [["Root"], ["Rules"]] := by
  native_decide

/- Guard admission is model-relative, and a target-presence guard is rejected independently of the checked expression. -/
example :
    tableError? [literalRow? (.fieldNotFilled 999) targetId 1] =
        some (.guardNotAdmitted 1) ∧
    tableError? [literalRow? (.fieldNotFilled targetId) targetId 1] =
        some (.guardTargetReference 1) := by
  native_decide

/- A guard the model does not admit is asked before any alternative's own class, as the Kernel asks a
guard naming nothing ahead of an unguarded alternative in either order (`settle2.tsv` C01 and C02):
the unadmitted guard answers here, and claims no class because its name was resolved by the caller. -/
example :
    tableError? [unguardedLiteralRow? targetId 1, literalRow? (.fieldFilled 999) targetId 2] =
        some (.guardNotAdmitted 2) ∧
    tableError? [literalRow? (.fieldFilled 999) targetId 2, unguardedLiteralRow? targetId 1] =
        some (.guardNotAdmitted 1) ∧
    NumericComputationTableError.diagnostic? (.guardNotAdmitted 2) = none := by
  native_decide

/- A guard reading its own target draws the reference class, in the only alternative and in a later
one, while an inadmissible guard claims none
([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)). -/
example :
    (tableError? [literalRow? (.fieldNotFilled targetId) targetId 1]).bind (·.diagnostic?) =
        some .errorReferenceToCalculatedField ∧
    (tableError? [literalRow? (.fieldFilled sourceId) targetId 1,
        literalRow? (.fieldFilled targetId) targetId 2]).bind (·.diagnostic?) =
        some .errorReferenceToCalculatedField ∧
    (tableError? [literalRow? (.fieldNotFilled 999) targetId 1]).bind (·.diagnostic?) = none := by
  native_decide

/- A false guard crosses row boundaries, but the first selected operation ends the scan even on numeric domain failure. -/
example :
    tableOutcome? [
      literalRow? (.fieldFilled laterId) targetId 1,
      literalRow? (.fieldNotFilled laterId) targetId 3] =
        some (.supported (.accepted { unscaled := 3, scale := 0 })) ∧
    tableOutcome? [
      divisionRow? (.fieldNotFilled laterId),
      literalRow? (.fieldNotFilled laterId) targetId 3] =
        some (.supported (.invalidNoValue .calculationValue)) := by
  native_decide

/- No selected guard is clean no-value; a poison reached during selection stops before a later holding row. -/
example :
    tableOutcome? [
      literalRow? (.fieldFilled sourceId) targetId 1,
      literalRow? (.fieldFilled laterId) targetId 3] =
        some (.supported .noValue) ∧
    tableOutcome? [
      literalRow? (.fieldFilled laterId) targetId 1,
      literalRow? (.fieldNotFilled sourceId) targetId 3]
      (context (later := (checkedNumber .empty).withFinding .malformed)) =
        some (.supported (.inheritedPoison .malformed)) := by
  native_decide

/-- The fixture beside a scale-2 Number, so one alternative's scale gate can fail. -/
private def fractionModel : FlatModel :=
  { model with fields := model.fields ++
      [{ numberDeclaration 35 "Frac" with policy := { kind := .number { scale := 2, signed := true } } }] }

/-- The class a whole computation draws, or the refusal's arm where it projects none. -/
private def tableClass
    (alternatives : List (Option ComputationCondition × AuthoredNumericExpr SurfaceNumericAtom))
    (suppress : Bool := false) : String :=
  match elaborateNumericTargetComputationTable fractionModel ["Root"] targetId alternatives
      suppress with
  | .ok _ => "admitted"
  | .error error =>
      (error.diagnostic?.map (·.kernelCode)).getD ("none:" ++ (reprStr error).takeWhile (!·.isWhitespace))

/-- A two-alternative computation guarded on `Source` and `Later`. -/
private def computationClass (first second : AuthoredNumericExpr SurfaceNumericAtom)
    (firstGuard : ComputationCondition := .fieldFilled sourceId) : String :=
  tableClass [(some firstGuard, first), (some (.fieldFilled laterId), second)]

/- The Kernel asks every alternative's other gates before a read of the target, so a self-read in one
alternative beside a scale mismatch or a second unbraced division in another draws that other class
in either order, and beside a later unresolved name that name's class; beside a clean alternative,
and from a guard, the self-read draws its own class, and two clean alternatives are admitted
([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards),
`settle.tsv` A01 to A10, `settle2.tsv` E01 and E02). -/
example :
    let target := surfaceField ["Root"] "Target"
    let source := surfaceField ["Root"] "Source"
    let later := surfaceField ["Root"] "Later"
    let frac := surfaceField ["Root"] "Frac"
    let two : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 2, authoredScale := 0 }
    let oneHalf : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 3 / 2, authoredScale := 1 }
    let divisions : AuthoredNumericExpr SurfaceNumericAtom := .binary .divide (.binary .divide source later) source
    [computationClass (.binary .multiply target two) (.binary .multiply source oneHalf),
      computationClass (.binary .multiply source oneHalf) (.binary .multiply target two),
      computationClass target frac, computationClass frac target,
      computationClass target divisions, computationClass divisions target,
      computationClass target later, computationClass source frac,
      computationClass source frac (firstGuard := .fieldFilled targetId),
      computationClass source later (firstGuard := .fieldFilled targetId),
      computationClass source later] =
      ["MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES",
        "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES",
        "MVK_TOO_MANY_DIV_FOR_CALC", "MVK_TOO_MANY_DIV_FOR_CALC",
        "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD", "MVK_INVALID_COMPARE_DEC_PLACES",
        "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD", "admitted"] ∧
    computationClass target (surfaceField ["Root"] "Nope") = "MVK_INVALID_ENTITY" := by
  native_decide

/- The two stages the Kernel asks, on the second settling grid
([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards),
`settle2.tsv`). An unguarded alternative among several refuses once, wherever it stands, and its own
read of the target goes unreported, while a guarded alternative's read ahead of it answers first. An
unguarded alternative's own scale or division class, and any alternative's scale mismatch, still
answers ahead of every alternative class. -/
example :
    let target := surfaceField ["Root"] "Target"
    let source := surfaceField ["Root"] "Source"
    let later := surfaceField ["Root"] "Later"
    let frac := surfaceField ["Root"] "Frac"
    let two : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 2, authoredScale := 0 }
    let g1 := some (ComputationCondition.fieldFilled sourceId)
    let g2 := some (ComputationCondition.fieldFilled laterId)
    let gT := some (ComputationCondition.fieldFilled targetId)
    [tableClass [(none, target), (g2, source)], tableClass [(g1, source), (none, target)],
      tableClass [(none, .binary .multiply target two), (g2, source)],
      tableClass [(none, target), (none, source)], tableClass [(none, source), (g2, target)],
      tableClass [(g1, target), (none, source)], tableClass [(gT, source), (none, target)],
      tableClass [(none, target), (g2, target)], tableClass [(none, target)],
      tableClass [(g1, target), (none, source), (g2, target)],
      tableClass [(g1, source), (g2, later), (none, target)]] =
      ["MVK_ERROR_EMPTY_PRECONDITION", "MVK_ERROR_EMPTY_PRECONDITION",
        "MVK_ERROR_EMPTY_PRECONDITION", "MVK_ERROR_EMPTY_PRECONDITION",
        "MVK_ERROR_EMPTY_PRECONDITION", "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD",
        "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD", "MVK_ERROR_EMPTY_PRECONDITION",
        "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD", "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD",
        "MVK_ERROR_EMPTY_PRECONDITION"] ∧
    [tableClass [(none, frac), (g2, source)],
      tableClass [(none, .binary .divide (.binary .divide source later) source), (g2, source)],
      tableClass [(g1, frac), (none, target)], tableClass [(gT, target), (g2, frac)]] =
      ["MVK_INVALID_COMPARE_DEC_PLACES", "MVK_TOO_MANY_DIV_FOR_CALC",
        "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES"] := by
  native_decide

/- A stage-ordered account fails here: the first alternative failing any other gate answers, a scale
mismatch ahead of an unresolved name or a second division, and a nested power or a second division ahead
of a mismatch or a name (`settle2.tsv` O01 to O10). -/
example :
    let source := surfaceField ["Root"] "Source"
    let later := surfaceField ["Root"] "Later"
    let frac := surfaceField ["Root"] "Frac"
    let nope := surfaceField ["Root"] "Nope"
    let two : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 2, authoredScale := 0 }
    let divisions : AuthoredNumericExpr SurfaceNumericAtom :=
      .binary .divide (.binary .divide source later) source
    let power : AuthoredNumericExpr SurfaceNumericAtom := .power (.power source two) two
    [computationClass frac nope, computationClass nope frac, computationClass frac divisions,
      computationClass power frac, computationClass divisions nope] =
      ["MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_ENTITY", "MVK_INVALID_COMPARE_DEC_PLACES",
        "MVK_TOO_MANY_POW_FOR_CALC", "MVK_TOO_MANY_DIV_FOR_CALC"] := by
  native_decide

/- A nested power and a String operand in an addition are asked in their own alternative's place too:
each answers ahead of a later unresolved name and behind an earlier one (`settle2.tsv` C03 to C06). The
String operand's own class is not projected, because the Kernel picks it by the operator and the other
operand's kind, `MVK_NO_STRING_OR_NUMBER_FOR_ADD` here, and this refusal is raised at the operand. -/
example :
    let source := surfaceField ["Root"] "Source"
    let nope := surfaceField ["Root"] "Nope"
    let text := surfaceField ["Root"] "Wrong"
    let two : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 2, authoredScale := 0 }
    let power : AuthoredNumericExpr SurfaceNumericAtom := .power (.power source two) two
    let mixed : AuthoredNumericExpr SurfaceNumericAtom := .binary .add source text
    [computationClass power nope, computationClass nope power, computationClass nope mixed] =
        ["MVK_TOO_MANY_POW_FOR_CALC", "MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY"] ∧
      (elaborateNumericTargetComputationTable fractionModel ["Root"] targetId
          [(some (.fieldFilled sourceId), mixed), (some (.fieldFilled laterId), nope)] matches
        .error (.operation 1 _)) := by
  native_decide

/- A guard reading the target beside a guard the model does not admit meets the unadmitted guard first
in either order, where the Kernel reports that guard's unresolved name; beside an admitted guard it draws
the reference class (`settle2k.tsv` R01 to R03). -/
example :
    let source := surfaceField ["Root"] "Source"
    let unresolved := some (ComputationCondition.fieldFilled 999)
    (elaborateNumericTargetComputationTable fractionModel ["Root"] targetId
        [(some (.fieldFilled targetId), source), (unresolved, source)] matches
      .error (.table (.guardNotAdmitted 2))) ∧
    (elaborateNumericTargetComputationTable fractionModel ["Root"] targetId
        [(unresolved, source), (some (.fieldFilled targetId), source)] matches
      .error (.table (.guardNotAdmitted 1))) ∧
    tableClass [(some (.fieldFilled targetId), source), (some (.fieldFilled laterId), source)] =
      "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD" := by
  native_decide

/- A guard is resolved before it reaches the elaborator, so one naming no field meets it as an
unadmitted guard. It is asked in its alternative's place: ahead of a later scale mismatch, behind an
earlier one. The Kernel's class for the unresolved name, `MVK_INVALID_ENTITY`, is the caller's to
project. -/
example :
    let source := surfaceField ["Root"] "Source"
    let frac := surfaceField ["Root"] "Frac"
    let unresolved := some (ComputationCondition.fieldFilled 999)
    tableClass [(unresolved, source), (some (.fieldFilled laterId), frac)] = "none:A12Kernel.NumericComputationTableElabError.table" ∧
      (elaborateNumericTargetComputationTable fractionModel ["Root"] targetId
          [(unresolved, source), (some (.fieldFilled laterId), frac)] matches
        .error (.table (.guardNotAdmitted 1))) ∧
      tableClass [(some (.fieldFilled sourceId), frac), (unresolved, source)] =
        "MVK_INVALID_COMPARE_DEC_PLACES" := by
  native_decide

/- Suppression is the whole computation's and lifts only the scale gate: a read of the target, a
second division, an unresolved name or an unguarded alternative then answers, and a sole scale-2 copy
is admitted. -/
example :
    let target := surfaceField ["Root"] "Target"
    let source := surfaceField ["Root"] "Source"
    let later := surfaceField ["Root"] "Later"
    let frac := surfaceField ["Root"] "Frac"
    let g1 := some (ComputationCondition.fieldFilled sourceId)
    let g2 := some (ComputationCondition.fieldFilled laterId)
    [tableClass [(g1, target), (g2, frac)] true, tableClass [(g1, frac), (g2, target)] true,
      tableClass [(g1, frac), (g2, .binary .divide (.binary .divide source later) source)] true,
      tableClass [(g1, frac), (g2, surfaceField ["Root"] "Nope")] true,
      tableClass [(none, frac)] true, tableClass [(none, target), (g2, frac)] true,
      tableClass [(none, frac), (g2, source)] true] =
      ["MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD", "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD",
        "MVK_TOO_MANY_DIV_FOR_CALC", "MVK_INVALID_ENTITY", "admitted",
        "MVK_ERROR_EMPTY_PRECONDITION", "MVK_ERROR_EMPTY_PRECONDITION"] := by
  native_decide

/-- The class a whole computation with a common precondition draws. -/
private def commonClass (common : ComputationCondition)
    (alternatives : List (Option ComputationCondition × AuthoredNumericExpr SurfaceNumericAtom)) :
    String :=
  match elaborateNumericTargetComputationTable fractionModel ["Root"] targetId alternatives
      (commonPrecondition := some common) with
  | .ok _ => "admitted"
  | .error error =>
      (error.diagnostic?.map (·.kernelCode)).getD ("none:" ++ (reprStr error).takeWhile (!·.isWhitespace))

/- A common precondition is no alternative's own guard: several alternatives without their own still
refuse as unguarded, and the common precondition's reads of the target are judged once, at the first
alternative the walk judges, so they go unjudged when it judges none and answer behind an earlier
unguarded alternative (`self-read-alternative-walk-2026-10-02/static.tsv` C01, C02, C05, C07, C08, C10,
C11). -/
example :
    let source := surfaceField ["Root"] "Source"
    let later := surfaceField ["Root"] "Later"
    let g := some (ComputationCondition.fieldFilled laterId)
    let ownTarget := ComputationCondition.fieldFilled targetId
    let other := ComputationCondition.fieldFilled sourceId
    let selfRead := surfaceField ["Root"] "Target"
    [commonClass other [(none, source), (none, later)], commonClass ownTarget [(none, source), (none, later)],
      commonClass ownTarget [(none, selfRead), (none, later)],
      commonClass ownTarget [(g, source), (none, later)], commonClass ownTarget [(none, source), (g, later)],
      commonClass ownTarget [(g, source)], commonClass ownTarget [(none, source)],
      commonClass other [(none, source)]] =
      ["MVK_ERROR_EMPTY_PRECONDITION", "MVK_ERROR_EMPTY_PRECONDITION", "MVK_ERROR_EMPTY_PRECONDITION",
        "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD", "MVK_ERROR_EMPTY_PRECONDITION",
        "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD", "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD",
        "admitted"] := by
  native_decide

/- The target's own lookup and the model's validation are no operand's reference, so neither claims the
resolver class an operand's failure projects: a repeatable target would otherwise claim
`MVK_NO_WILDCARD` and a model refusing its own declaration `MVK_FRACT_DIGITS_INVALID`. The default
fixed scope refuses a repeatable target; the row scope admits one contained in the declaring group at
its reading scope, which no scalar executor accepts, refuses one outside it with the placement class
([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-row-target-boundary)), and
refuses a fixed target. -/
example :
    let source := surfaceField ["Root"] "Source"
    let badModel : FlatModel := { model with fields := model.fields ++
      [{ numberDeclaration 40 "Bad" with numericTargetConstraints := { minFractionalDigits := 3 } }] }
    (match elaborateNumericTargetComputationTable model ["Root"] repeatedId [(none, source)] with
      | .error error@(.operation 1 (.targetResolve (.repeatableReference _))) => error.diagnostic?.isNone
      | _ => false : Bool) = true ∧
    (match elaborateNumericTargetComputationTable model ["Root"] repeatedId [(none, source)]
        (targetScope := .row) with
      | .ok table => table.readingScope == [10] && !table.supportsScalarEvaluation &&
          table.atomsSupportScalarEvaluation
      | .error _ => false : Bool) = true ∧
    (match elaborateNumericTargetComputationTable model ["Other"] repeatedId [(none, source)]
        (targetScope := .row) with
      | .error error@(.operation 1 (.repeatableTarget (.targetOutsideDeclaringGroup _ _))) =>
          error.diagnostic? == some .fieldNotInRuleGroup
      | _ => false : Bool) = true ∧
    (match elaborateNumericTargetComputationTable model ["Root"] targetId [(none, source)]
        (targetScope := .row) with
      | .error error@(.operation 1 (.repeatableTarget (.targetNotRepeatable _))) =>
          error.diagnostic?.isNone
      | _ => false : Bool) = true ∧
    (match elaborateNumericTargetComputationTable model ["Root"] 999 [(none, source)] with
      | .error error@(.operation 1 (.targetResolve (.unknownFieldId 999))) => error.diagnostic?.isNone
      | _ => false : Bool) = true ∧
    (match elaborateNumericTargetComputationTable badModel ["Root"] targetId [(none, source)] with
      | .error error@(.operation 1 (.invalidModel _)) => error.diagnostic?.isNone
      | _ => false : Bool) = true := by
  native_decide

end A12Kernel.Conformance.NumericComputation.Table
