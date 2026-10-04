import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.Replay

/-! # Locks for the leaf carrier dispatch

`lowerCondition` offers each leaf to its carriers in order, so a carrier can be unreachable when an
earlier pattern claims its shape. Each case pins one shape to the carrier that must admit it.
-/

namespace A12Kernel.Dm.LowerLocks

open A12Kernel A12Kernel.Dm

private def model : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Order"], name := "Ref", policy := { kind := .string } },
      { id := 3, groupPath := ["Order", "Head"], name := "Code", policy := { kind := .string } },
      { id := 4, groupPath := ["Order"], name := "Amt", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 2, groupPath := ["Order", "Rows"], name := "Note", policy := { kind := .string },
        repeatableScope := [10] },
      { id := 10, groupPath := ["Order", "Rows"], name := "Filter", policy := { kind := .string },
        repeatableScope := [10] },
      { id := 5, groupPath := ["Order"], name := "Due1", policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { id := 6, groupPath := ["Order"], name := "Due2", policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { id := 7, groupPath := ["Other"], name := "O", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 8, groupPath := ["Order"], name := "Amt2", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 9, groupPath := ["Order", "Tail"], name := "T", policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Order", "Rows"], repeatability := some 5 }] }

private def admitted (text : String) : Bool :=
  match parseText .english text with
  | .ok parsed => (lowerCondition model ["Order"] false parsed.body).toOption.isSome
  | .error _ => false

example :
    [admitted "FirstFilledValue(Rows*/Note, Ref) == \"x\"",
     admitted "\"x\" != FirstFilledValue(Rows*/Note, Ref)",
     admitted "FirstFilledValue(Rows*/Note) == FirstFilledValue(Ref, Head/Code)",
     !admitted "FirstFilledValue(Rows*/Note) > \"x\""].all id := by
  native_decide

example : (do
    let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    let rule : DmRule := {
      group := ["Order"]
      name := "R"
      errorCode := "R"
      errorEntityRelPath := "../Ref"
      condition := "FirstFilledValue(Rows*/Note Having [Rows/Filter] == \"keep\", Ref) != \"x\"", severity := "ERROR" }
    let checked ← (checkRule dm .english rule).toOption
    let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler model).toOption
    let document ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [] }).toOption
    let partialResult ← (checked.evalOrdinaryOncePartial document .full).toOption
    pure (checked.hasHaving, checked.condition.core.referencesField 10,
      checked.condition.core.referencesErrorField 10, partialResult)) =
    some (true, true, false, .skipped) := by native_decide


example :
    [admitted "FieldFilled(Ref) And MinValue(Due1, Due2) == [Due1]",
     admitted "[Due2] >= MaxValue(Due1, Due2)",
     admitted "MinValue(Due1, Due2) <= MaxValue(Due1, Due2)",
     !admitted "MinValue(Due1, Due2) == [Amt]",
     !admitted "MinValue(Due1) == [Due1]"].all id := by
  native_decide


private def temporalReferences : Option (Bool × List FieldId) := do
  let source ← model.fields[5]?
  let third := { source with id := 11, name := "Due3" }
  let dm := { model with fields := model.fields ++ [third] }
  let parsed ← (parseText .english "MinValue(Due1, Due2) == [Due3]").toOption
  let condition ← (lowerCondition dm ["Order"] false parsed.body).toOption
  let pointers ← (condition.core.referencePointers []).toOption
  pure (condition.core.referencesErrorField 11, pointers.map (·.field))

example : temporalReferences = some (true, [5, 6, 11]) := by
  native_decide

example :
    (do
      let source ← model.fields[5]?
      let partialField := { source with
        id := 11
        name := "Partial"
        temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } }
      let dm := { model with fields := model.fields ++ [partialField] }
      let parsed ← (parseText .english "MinValue(Due1, Due2) == [Partial]").toOption
      pure (!(lowerCondition dm ["Order"] false parsed.body).isOk)) = some true := by
  native_decide

private def temporalCell (value : Value) : CheckedCell :=
  { rawPresent := true, parsed := some value, findings := [] }

private def temporalDate (month : Nat) : CheckedCell :=
  temporalCell (.temporal (.date {
    instant := (DateParts.LegacyHybrid.midnightInstant? { year := 2024, month, day := 1 }).getD { epochMillis := 0 },
    parts := { year := 2024, month, day := 1 },
    basis := .storedGregorian }))

private def temporalEval (dm : FlatModel) (text : String)
    (first second : CheckedCell) : Option Verdict := do
  let parsed ← (parseText .english text).toOption
  let condition ← (lowerCondition dm ["Order"] false parsed.body).toOption
  pure (condition.core.evalSelected { fields := {
    read := fun id => if id == 5 then first else if id == 6 then second else
      { rawPresent := false, parsed := none, findings := [] } }, groups := fun _ => none })

example :
    ["==", "!=", "<", "<=", ">", ">="].map
      (fun op => temporalEval model s!"MinValue(Due1, Due2) {op} [Due2]"
        (temporalDate 1) (temporalDate 2)) =
      [some .notFired, some (.fired .value), some (.fired .value),
       some (.fired .value), some .notFired, some .notFired] := by
  native_decide

example :
    temporalEval model "MinValue(Due1, Due2) == [Due2]"
      { rawPresent := false, parsed := none, findings := [] } (temporalDate 2) =
        some (.fired .omission) ∧
    temporalEval model "MinValue(Due1, Due2) == [Due2]"
      { rawPresent := true, parsed := none, findings := [.dateFormat] } (temporalDate 2) =
        some .unknown ∧
    temporalEval model "MinValue(Due1, Due2) == MaxValue(Due1, Due2)"
      { rawPresent := false, parsed := none, findings := [] }
      { rawPresent := false, parsed := none, findings := [] } = some .notFired := by
  native_decide

private def temporalProfile (kind : TemporalKind) (components : TemporalComponents)
    (format : String) : FlatModel :=
  { model with fields := model.fields.map fun field =>
      if field.id == 5 || field.id == 6 then
        { field with
          policy := { kind := .temporal kind components }
          temporalTargetPolicy := some { format } }
      else field }

private def clockValue : TimeOfDay := ⟨12, 30, 0, by decide, by decide, by decide⟩

private def temporalStamp (instant : Int) : CheckedCell :=
  temporalCell (.temporal (.dateTime { epochMillis := instant }
    { year := 2024, month := 10, day := 27 } clockValue .storedGregorian))

example :
    temporalEval (temporalProfile .time TemporalComponents.time "HH:mm:ss")
      "MinValue(Due1, Due2) == [Due2]"
      (temporalCell (.temporal (.time { epochMillis := 1 } clockValue)))
      (temporalCell (.temporal (.time { epochMillis := 2 } clockValue))) =
        some (.fired .value) ∧
    temporalEval (temporalProfile .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss")
      "MaxValue(Due1, Due2) == [Due2]" (temporalStamp 1) (temporalStamp 2) =
        some (.fired .value) ∧
    temporalEval (temporalProfile .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss")
      "MinValue(Due1, Due2) == [Due2]" (temporalStamp 1) (temporalStamp 2) =
        some .notFired := by
  native_decide

example :
    [admitted "Valid(Ref, \"NoSuchType\")",
     admitted "Invalid(Ref, \"NoSuchType\") Or FieldFilled(Amt)",
     !admitted "Valid(Amt, \"NoSuchType\")",
     !admitted "Valid(Ref, \"\")",
     !admitted "Valid(Rows*/Note, \"NoSuchType\")"].all id := by
  native_decide

private def validityReplay (registered : Bool) (value : String)
    (expectedCodes : List String) : Option (List String) := do
  let world : World := {
    now := { epochMillis := 0 }
    customFieldValidator? := fun name => if registered && name == "Code" then
      some (fun value _ => if value == "ok" then none else some { projectCode := "bad" })
      else none }
  let rule (code operation : String) : DmRule := {
    group := ["Order"], name := code, errorEntityRelPath := "../Ref", errorCode := code
    condition := s!"FieldFilled(Ref) And ({operation}(Ref, \"Code\"))", severity := "ERROR" }
  let dm : DmModel := {
    flat := model, rules := [rule "V" "Valid", rule "I" "Invalid"]
    computations := [], conditionLanguage := "en_US", refusals := [] }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := if value.isEmpty then [] else [
    { address := { field := 1, path := [] }, stored := value, raw := .parsed (.str value) }] }).toOption
  let expected := expectedCodes.map fun code =>
    { code, pointer := "Order/Ref", messageType := "VALUE_ERROR", severity := "ERROR" }
  pure ((replayRules dm .english world document expected).map (·.status.tier))


example : validityReplay true "ok" ["V"] = some ["match", "match"] ∧
    validityReplay true "bad" ["I"] = some ["match", "match"] ∧
    validityReplay false "ok" ["V", "I"] = some ["match", "match"] ∧
    validityReplay false "" [] = some ["match", "match"] := by
  native_decide

example :
    [admitted "FieldValuesNotUnique(Amt, Amt2) And FieldFilled(Ref)",
     admitted "FieldValuesNotUnique(Rows*/Note)",
     admitted "FieldValuesNotUnique(Rows*)",
     admitted "FieldValuesNotUnique(Head)",
     admitted "FieldValuesNotUnique(Due1, Due2)",
     !admitted "FieldValuesNotUnique(Ref, Amt)",
     !admitted "FieldValuesNotUnique(Ref)"].all id := by
  native_decide

example :
    [admitted "AtLeastOneFieldValueIncludedInValueList(Rows*/Note In Ref) And FieldFilled(Ref)",
     admitted "NoFieldValueIncludedInValueList(Rows* In Ref) Or FieldNotFilled(Ref)",
     admitted "NotAllFieldValuesIncludedInValueList(Tail In Amt)",
     admitted "AtLeastOneFieldValueIncludedInValueList(Rows*/Note In \"x\")"].all id := by
  native_decide

example :
    (do
      let parsed ← (parseText .english
        "AtLeastOneFieldValueIncludedInValueList(Rows*/Note Having ([Rows/Filter] == \"x\" And [$Head/Code] == \"x\") In \"x\")").toOption
      let checked ← (lowerCondition model ["Order"] false parsed.body).toOption
      pure (checked.hasHaving,
        [1, 2, 3, 10].filter checked.core.referencesField,
        [1, 2, 3, 10].filter checked.core.referencesErrorField,
        (checked.core.referencePointers []).toOption)) =
      some (true, [2, 3, 10], [2, 3], some [
        { field := 2, coordinates := [.wildcard] },
        { field := 10, coordinates := [.wildcard] },
        { field := 3, coordinates := [] }]) := by
  native_decide

example :
    (do
      let parsed ← (parseText .english
        "FieldValuesNotUnique(Rows*/Note Having ([Rows/Filter] == \"x\" And [$Head/Code] == \"x\"))").toOption
      let checked ← (lowerCondition model ["Order"] false parsed.body).toOption
      pure (checked.hasHaving,
        [1, 2, 3, 10].filter checked.core.referencesField,
        [1, 2, 3, 10].filter checked.core.referencesErrorField,
        (checked.core.referencePointers []).toOption)) =
      some (true, [2, 3, 10], [2, 3], some [
        { field := 2, coordinates := [.wildcard] },
        { field := 10, coordinates := [.wildcard] },
        { field := 3, coordinates := [] }]) := by
  native_decide

private def numericFilterModel : FlatModel :=
  { model with fields := model.fields ++ [
      { id := 11, groupPath := ["Order", "Rows"], name := "N", repeatableScope := [10],
        policy := { kind := .number { scale := 0, signed := true } } }] }

example :
    (do
      let parsed ← (parseText .english
        "FieldValuesNotUnique(Rows*/Note Having [Rows/N] + 1 < [$Amt] + CurrentRepetition(Rows))").toOption
      let checked ← (lowerCondition numericFilterModel ["Order"] false parsed.body).toOption
      pure ([2, 4, 11].filter checked.core.referencesField,
        [2, 4, 11].filter checked.core.referencesErrorField,
        (checked.core.referencePointers []).toOption)) =
      some ([2, 4, 11], [2, 4], some [
        { field := 2, coordinates := [.wildcard] },
        { field := 11, coordinates := [.wildcard] },
        { field := 4, coordinates := [] }]) := by
  native_decide

/- The Base-Year ladder's literal endpoints must reach the shared numeric carrier, including the
reversed mixed endpoint. Invalid calendar text stays outside it (spec/05 §1). -/
example :
    [admitted "DifferenceInDays(\"28.02.\", \"01.03.\") > 1",
     admitted "DifferenceInDays(\"01.01.2024\", Due1) == 0",
     admitted "DifferenceInDays(Due1, \"01.01.2024\") == 0",
     !admitted "DifferenceInDays(\"29.02.\", \"01.03.\") == 1"].all id := by
  native_decide

/- A one-operand group-list quantifier reaches the group-list carrier rather than stopping at the
one-argument presence arm, which admits only `FieldFilled` and `GroupFilled` forms. -/
example :
    [admitted "NoGroupFilled(Rows*)", admitted "AtLeastOneGroupFilled(Rows*)",
     admitted "FieldFilled(Ref)", admitted "GroupFilled(Rows)"].all id := by
  native_decide

/- A category projects a field's value; on a group operand it has nothing to project, so the operand
is refused rather than read as the bare group. -/
example :
    [admitted "AtLeastOneFieldFilled(Head)", !admitted "AtLeastOneFieldFilled(Head -> Code)"].all id := by
  native_decide

/- The count-expression grid admits fractional ordering on both sides while equality retains
its scale gate. The arithmetic route must preserve the literal instead of truncating it. -/
example :
    [admitted "NumberOfFilledFields(Head) < 2", admitted "NumberOfFilledFields(Head) < 1.5",
     admitted "1.5 > NumberOfFilledFields(Head)", admitted "NumberOfFilledFields(Head) + 1 < 1.5",
     !admitted "NumberOfFilledFields(Head) == 1.0", !admitted "1.5 != NumberOfFilledFields(Head)"].all id := by
  native_decide

/- `NumberOfDifferentValues` reaches the String/Enumeration and temporal carriers once the Number one
refuses its list, a star-free group operand included, which lowers to the scalar surface first; a
list mixing the families stays refused. A plain second-root read belongs to the ordinary bound
numeric carrier, without requiring an entity-list operand. -/
example :
    [admitted "NumberOfDifferentValues(Ref, Head/Code) == 1", admitted "NumberOfDifferentValues(Rows*/Note) > 1",
     admitted "NumberOfDifferentValues(Head) > 0", admitted "NumberOfDifferentValues(Due1, Due2) == 1",
     !admitted "NumberOfDifferentValues(Ref, Due1) == 1", admitted "[/Other/O] + [Amt] < 5"].all id := by
  native_decide

private def admittedSuppressed (text : String) : Bool :=
  match parseText .english text with
  | .ok parsed => (lowerCondition model ["Order"] true parsed.body).toOption.isSome
  | .error _ => false

/- The exact-scale gate holds ahead of the flat carrier, which would otherwise admit a literal whose
decimal places a scale-0 field refuses; the suppression preamble lifts it. -/
example :
    [admitted "[Amt] == 1", !admitted "[Amt] == 1.00", !admitted "FieldFilled(Ref) And 1.00 == [Amt]",
     admittedSuppressed "[Amt] == 1.00"].all id := by
  native_decide

private def ruleAt (errorPath : String) : DmRule :=
  { group := ["Order"], name := "R", errorEntityRelPath := errorPath, errorCode := "E"
    condition := "FieldFilled(Ref)", severity := "ERROR" }

/- An error path is written one step below the rule group; one without that step is refused rather
than read at the group, while the written form resolves. -/
example :
    let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US",
                          refusals := [] }
    [(checkRule dm .english (ruleAt "../Ref")).toOption.isSome,
     (checkRule dm .english (ruleAt "Ref")).toOption.isNone].all id := by
  native_decide

private def ancestorModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe", "Outer"], name := "Marker", policy := { kind := .string },
        repeatableScope := [10] },
      { id := 2, groupPath := ["Probe", "Outer", "Flat"], name := "A", policy := { kind := .string },
        repeatableScope := [10] },
      { id := 3, groupPath := ["Probe", "Outer", "Peer"], name := "B", policy := { kind := .string },
        repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Probe", "Outer"], repeatability := some 3 }] }

/- A group count over fixed groups below the rule's repeatable row lowers onto a carrier the row
iteration runs, as the Kernel evaluates it per row
([capture](../../../evidence/kernel-30.8.1/captures/fixed-group-repeatable-ancestor-carriers/request.json)). -/
example :
    let dm : DmModel := { flat := ancestorModel, rules := [], computations := [],
                          conditionLanguage := "en_US", refusals := [] }
    let rule : DmRule := { group := ["Probe", "Outer"], name := "R", errorEntityRelPath := "../Marker"
                           errorCode := "E", severity := "ERROR"
                           condition := "FieldFilled(Marker) And NumberOfFilledGroups(Flat, Peer) == 2" }
    ((checkRule dm .english rule).toOption.map (·.condition.core.supportsOrdinaryIteration)) ==
      some true := by
  native_decide

/- The scale warning is the only suppressible name; a rule suppressing any other is refused. -/
example :
    let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US",
                          refusals := [] }
    let rule (condition : String) : DmRule := { ruleAt "../Ref" with condition }
    [(checkRule dm .english (rule "@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES) FieldFilled(Ref)")).toOption.isSome,
     (checkRule dm .english (rule "@SuppressWarning(Late_Fee) FieldFilled(Ref)")).toOption.isNone].all id := by
  native_decide

/- The reader keeps a computation's common precondition apart from each alternative's own guard, so
two alternatives without their own still refuse as unguarded, while one alternative under it is
admitted (`self-read-alternative-walk-2026-10-02/static.tsv` C05). -/
example :
    let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US",
                          refusals := [] }
    let computation (alternatives : List DmAlternative) : DmComputation :=
      { group := ["Order"], name := "C", targetRelPath := "../Amt", commonPrecondition := some "FieldFilled(Ref)"
        alternatives, errorCodesToSuppress := [] }
    [(lowerComputation dm.flat .english (computation [{ precondition := none, operation := "1" },
        { precondition := none, operation := "2" }])).toOption.isNone,
     (lowerComputation dm.flat .english (computation [{ precondition := none, operation := "1" }])).toOption.isSome].all id := by
  native_decide

example :
    let computation (guard : String) : DmComputation :=
      { group := ["Order"], name := "C", targetRelPath := "../Amt", commonPrecondition := some guard
        alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }
    ["[Amt2] + 1 > 0", "1 < [Amt2] + 2", "Abs([Amt2]) == 2",
      "[Amt2] != 0 And FieldFilled(Ref)", "[Amt2] >= 0", "0 <= [Amt2]"].all (fun guard =>
        (lowerComputation model .english (computation guard)).toOption.isSome) := by
  native_decide

example :
    let computation (guard : String) (suppressed : List String := []) : DmComputation :=
      { group := ["Order"], name := "C", targetRelPath := "../Amt", commonPrecondition := some guard
        alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := suppressed }
    [!(lowerComputation model .english (computation "[Amt] > 0")).toOption.isSome,
     !(lowerComputation model .english (computation "[Ref] > 0")).toOption.isSome,
     !(lowerComputation model .english (computation "1 > 0")).toOption.isSome,
     !(lowerComputation model .english (computation "[Amt2] == 1.50")).toOption.isSome,
     (lowerComputation model .english (computation "[Amt2] == 1.50"
       ["MVK_INVALID_COMPARE_DEC_PLACES"])).toOption.isSome,
     (lowerComputation model .english (computation "[Amt2] > 1.50")).toOption.isSome].all id := by
  native_decide

example :
    let computation (guard : String) : DmComputation :=
      { group := ["Order"], name := "C", targetRelPath := "../Amt", commonPrecondition := some guard
        alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }
    ["[Ref] == \"A\"", "\"A\" != [Ref]", "[Ref] == [Head/Code]",
      "[Ref] != \"\" Or FieldFilled(Head/Code)"].all (fun guard =>
        (lowerComputation model .english (computation guard)).toOption.isSome) := by
  native_decide

private def textGuard (text : String) : Option (CheckedComputationCondition model) := do
  let parsed ← (parseText .english text).toOption
  let surface ← (lowerGuard model ["Order"] false parsed.body).toOption
  (model.elaborateCheckedComputationCondition ["Order"] ["Order"] surface).toOption

private def textGuardEval (text : String) (first second : CheckedCell) :
    Option ComputationConditionResult := do
  let guard ← textGuard text
  (guard.evalChecked { read := fun id => if id == 1 then first else second }).toOption

private def textEmpty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def textBad : CheckedCell := formalCheck { kind := .string } (.rejected .malformed)

example :
    let good := temporalCell (.str "A")
    [textGuardEval "[Ref] == [Head/Code]" textEmpty textBad,
     textGuardEval "[Ref] == \"\"" textBad good,
     textGuardEval "[Ref] == \"\"" good good,
     textGuardEval "[Ref] != \"A\"" textEmpty good,
     textGuardEval "[Ref] != \"A\" And [Head/Code] == \"A\"" good textBad,
     textGuardEval "[Ref] == \"A\" Or [Head/Code] == \"A\"" good textBad] =
      [some (.poison .malformed), some (.poison .malformed), some .notTrue,
       some .notTrue, some .notTrue, some .holds] := by
  native_decide

example :
    (textGuard "[Ref] == [Head/Code]").map (fun guard =>
      (guard.referencesField 1, guard.referencesField 3, guard.referencesField 4)) =
        some (true, true, false) ∧
    !(ComputationCondition.wellFormedBool (.leaf (.text (.number (.ordinary .equal)
      { id := 4, info := { scale := 0, signed := true } } 1))) model) := by
  native_decide

private def enumGuardModel : FlatModel :=
  { model with fields := model.fields ++ [{ id := 11, groupPath := ["Order"], name := "E", policy := { kind := .enumeration }, enumeration := some { storedTokens := ["A", "B"], categories := [{ name := "Kind", tokens := ["X", "Y"] }] } }] }

private def enumGuardEval (text : String) : Option ComputationConditionResult := do
  let parsed ← (parseText .english text).toOption
  let surface ← (lowerGuard enumGuardModel ["Order"] false parsed.body).toOption
  let guard ← (enumGuardModel.elaborateCheckedComputationCondition ["Order"] ["Order"] surface).toOption
  (guard.evalChecked { read := fun field =>
    if field == 11 then temporalCell (.enum "A") else temporalCell (.str "X") }).toOption

example :
    [enumGuardEval "[E] == \"A\"", enumGuardEval "\"B\" != [E]",
     enumGuardEval "[E -> Kind] == \"X\"", enumGuardEval "[E -> Kind] == [Ref]",
     enumGuardEval "[Ref] == [E -> Kind]", enumGuardEval "[E] == \"BAD\"",
     enumGuardEval "[E] == \"\"", enumGuardEval "[E] > \"A\""] =
      [some .holds, some .holds, some .holds, some .holds, some .holds, none, none, none] := by
  native_decide

private def textReadDiagnostic (field : String) : Option KernelStaticDiagnostic :=
  let rawModel := { model with fields := model.fields.map fun declaration =>
    if declaration.id == 1 then
      { declaration with
        stringValueMode := .raw
        stringPolicy := { lineBreaksPermitted := true } }
    else declaration }
  match elaborateNumericTargetComputationTableFromSurface rawModel ["Order"] 4
      [(some (.text .equal (.direct { base := .relative 0, groups := [], field }) (.inr "A")),
        .literal { value := 1, authoredScale := 0 })] with
  | .ok _ => none
  | .error error => error.diagnostic?

example : [textReadDiagnostic "Ref", textReadDiagnostic "Head"] =
    [some .rawTypeOperandInvalid, some .noGroupsAllowed] := by
  native_decide

private def rowModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Order", "Rows"], name := "Due", policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" }, repeatableScope := [10] },
      { id := 2, groupPath := ["Order", "Rows"], name := "Flag", policy := { kind := .boolean }, repeatableScope := [10] },
      { id := 3, groupPath := ["Order", "Rows"], name := "Amt", policy := { kind := .number { scale := 0, signed := true } },
        repeatableScope := [10] },
      { id := 4, groupPath := ["Order", "Rows"], name := "Text", policy := { kind := .string }, repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Order", "Rows"], repeatability := some 5 }] }

example :
    let row : DmComputation :=
      { group := ["Order", "Rows"], name := "C", targetRelPath := "../Amt",
        commonPrecondition := some "[Text] == \"A\"",
        alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }
    (lowerComputation rowModel .english row).isOk ∧
    (do
      let parsed ← (parseText .english "[Rows/Note] == \"A\"").toOption
      let surface ← (lowerGuard model ["Order"] false parsed.body).toOption
      pure (!(model.elaborateCheckedComputationCondition ["Order"] ["Order"] surface).isOk)) = some true := by
  native_decide

/- A row target of a kind other than Number lowers onto the row step its operation names: a Date
literal, `True` and `FieldValueAsString` each admit, and an operation no row carrier names is refused. -/
example :
    let computation (target operation : String) : DmComputation :=
      { group := ["Order", "Rows"], name := "C", targetRelPath := "../" ++ target, commonPrecondition := none
        alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
    let admitted (target operation : String) :=
      (lowerComputation rowModel .english (computation target operation)).toOption.isSome
    [admitted "Due" "\"05.03.2024\"", admitted "Flag" "True", admitted "Text" "FieldValueAsString(Amt)",
     !admitted "Due" "[Amt]"].all id := by
  native_decide

/- A quoted literal is typed by its content before any operand reads it: a real date with or without
its year, a real clock and a date-time stamp are temporal constants, while a date missing its
trailing dot, an impossible day, a February 29 and a 24:00 clock stay strings. -/
example :
    ["05.03.2024", "05.03.", "30.04.", "12:30:00", "05.03.2024T12:30:00"].all isTemporalConstant &&
      !["05.03", "31.04.", "29.02.", "24:00:00", "12:30", "29.02.2023", "2024-03-05"].any
        isTemporalConstant := by
  native_decide

/- A temporal constant into a String target is refused at a fixed and at a row target alike, and a
string-shaped one admitted (`yearless-constant-family-2026-10-02/static.tsv` Y01, Y02, Y07–Y14);
opposite a text in a rule it is refused as well ([`spec/05`](../../../spec/05-dates-and-time.md) §1). -/
example :
    let computation (group : GroupPath) (target operation : String) : DmComputation :=
      { group, name := "C", targetRelPath := "../" ++ target, commonPrecondition := none
        alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
    let fixed (operation : String) :=
      (lowerComputation model .english (computation ["Order"] "Ref" operation)).toOption.isSome
    let row (operation : String) :=
      (lowerComputation rowModel .english (computation ["Order", "Rows"] "Text" operation)).toOption.isSome
    [!fixed "\"05.03.\"", !row "\"05.03.\"", !fixed "\"05.03.2024\"", !row "\"05.03.2024\"",
     fixed "\"05.03\"", row "\"05.03\"", fixed "\"31.04.\"", fixed "\"29.02.\"",
     !fixed "\"12:30:00\"", !row "\"12:30:00\"",
     !admitted "[Ref] == \"12:30:00\"", !admitted "[Ref] == \"05.03.\"",
     admitted "[Ref] == \"05.03\""].all id := by
  native_decide

private def gated (text : String) : Option Bool :=
  match parseText .english text with
  | .ok parsed => (lowerCondition model ["Order"] false parsed.body).toOption.map (·.core.canFireOnEmpty)
  | .error _ => none

/- A count on its small side lifts the empty-instance gate from anywhere in the condition, beneath
`And` beside a large-side twin too, while a count only on the large side does not; all three counts
and the right-hand sides of `>` and `>=` take part
([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-empty-gate-count-beneath-and)). -/
example :
    [gated "NumberOfFilledFields(Ref, Amt) < 1 And NumberOfFilledFields(Ref, Amt) >= 0",
     gated "2 > NumberOfFilledGroups(Head, Tail) + [Amt]", gated "1 >= NumberOfFilledGroups(Head, Tail) + [Amt]",
     gated "NumberOfDifferentValues(Amt, Amt2) < 1", gated "NumberOfDifferentValues(Ref, Head/Code) < 1",
     gated "NumberOfDifferentValues(Due1, Due2) < 1",
     gated "NumberOfFilledFields(Ref, Amt) >= 0 And [Amt] < 5", gated "-1 < NumberOfFilledGroups(Head, Tail) + [Amt]",
     gated "NumberOfDifferentValues(Amt, Amt2) >= 0", gated "NumberOfDifferentValues(Ref, Head/Code) >= 0",
     gated "NumberOfDifferentValues(Due1, Due2) >= 0"] =
      [some true, some true, some true, some true, some true, some true,
       some false, some false, some false, some false, some false] := by
  native_decide

/- A computation's suppressed codes are read as one preamble: the supported name padded is admitted,
and the same name twice is refused ([`spec/12`](../../../spec/12-concrete-syntax.md) §4). -/
example :
    let computation (codes : List String) : DmComputation :=
      { group := ["Order"], name := "C", targetRelPath := "../Amt", commonPrecondition := none
        alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := codes }
    let admitted (codes : List String) := (lowerComputation model .english (computation codes)).toOption.isSome
    [admitted [], admitted [" MVK_INVALID_COMPARE_DEC_PLACES "],
     !admitted ["MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES"],
     !admitted ["MVK_LATE"]].all id := by
  native_decide

private def repeatableRoot : FlatModel :=
  { fields := [{ id := 1, groupPath := ["Rep"], name := "P", policy := { kind := .number { scale := 0, signed := true } },
                 repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Rep"], repeatability := some 3 }] }

/- A once rule whose error field lies in a repeatable root runs with no content gate: over a document
without one row it fires once, at the first row
([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-rule-bucket-empty-gate) `REPSUM`). -/
example :
    let dm : DmModel := { flat := repeatableRoot, rules := [], computations := [], conditionLanguage := "en_US",
                          refusals := [] }
    let rule : DmRule := { group := ["Rep"], name := "R", errorEntityRelPath := "../P", errorCode := "R"
                           condition := "Sum(/Rep*/P) < 5", severity := "ERROR" }
    let world : World := { now := { epochMillis := 0 } }
    (do
      let checkedRule ← (checkRule dm .english rule).toOption
      let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler repeatableRoot).toOption
      let checked ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [] }).toOption
      let messages ← (runRule world checked checkedRule).toOption
      pure (messages.map fun message => renderPointer repeatableRoot message.errorAddress)) = some ["Rep/P"] := by
  native_decide

/- A fixed second-root read retains its scope certificate without introducing an iteration;
the content-gate reason is the static root pair (spec/03 A.4). -/
example :
    (match parseText .english "[/Other/O] + [Amt] < 5" with
      | .ok parsed => match lowerCondition model ["Order"] false parsed.body with
        | .ok checked =>
            checked.core.referencesMultipleRoots && !checked.core.requiresAddressedValidation
        | .error _ => false
      | .error _ => false) = true := by
  native_decide

private def enumerationModel : FlatModel :=
  let enumeration (id : FieldId) (groupPath : GroupPath) (name : String) (scope : List RepeatableLevel) :
      FlatFieldDecl :=
    { id, groupPath, name, policy := { kind := .enumeration }, repeatableScope := scope
      enumeration := some { storedTokens := ["A", "B"] } }
  { fields := [enumeration 1 ["Form"] "Fixed" [], enumeration 2 ["Form"] "First" [],
      enumeration 3 ["Form"] "Second" [], enumeration 4 ["Form", "Rows"] "Target" [10],
      enumeration 5 ["Form", "Rows", "Items"] "Choice" [10, 20]]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 },
      { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 3 }] }

/- An Enumeration `FirstFilledValue` lowers onto its fixed carrier over a list and onto its row
carrier over a star below the target's row. -/
example :
    let computation (group : GroupPath) (target operation : String) : DmComputation :=
      { group, name := "C", targetRelPath := "../" ++ target, commonPrecondition := none
        alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
    [(lowerComputation enumerationModel .english
        (computation ["Form"] "Fixed" "FirstFilledValue(First, Second)")).toOption.isSome,
     (lowerComputation enumerationModel .english
        (computation ["Form", "Rows"] "Target" "FirstFilledValue(Items*/Choice)")).toOption.isSome].all id := by
  native_decide

private def fragmentModel : FlatModel :=
  let fragment (id : FieldId) (groupPath : GroupPath) (name : String) (scope : List RepeatableLevel) :
      FlatFieldDecl :=
    { id, groupPath, name, policy := { kind := .temporal .date (TemporalComponents.ofFormat "yyyy-MM") }
      temporalTargetPolicy := some { format := "yyyy-MM" }, repeatableScope := scope }
  { fields := [fragment 1 ["Form"] "Fixed" [], fragment 2 ["Form"] "First" [],
      fragment 3 ["Form"] "Second" [], fragment 4 ["Form", "Rows", "Tasks"] "Target" [10, 30],
      fragment 5 ["Form", "Rows", "Choices"] "Choice" [10, 20]]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 },
      { level := 20, path := ["Form", "Rows", "Choices"], repeatability := some 3 },
      { level := 30, path := ["Form", "Rows", "Tasks"], repeatability := some 3 }] }

/- A DateFragment `FirstFilledValue`, its target read by its format, lowers onto the one fragment
carrier over a list at a fixed target and over a sibling star at a row target. -/
example :
    let computation (group : GroupPath) (target operation : String) : DmComputation :=
      { group, name := "C", targetRelPath := "../" ++ target, commonPrecondition := none
        alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
    [(lowerComputation fragmentModel .english
        (computation ["Form"] "Fixed" "FirstFilledValue(First, Second)")).toOption.isSome,
     (lowerComputation fragmentModel .english
        (computation ["Form", "Rows", "Tasks"] "Target" "FirstFilledValue(../Choices*/Choice)")).toOption.isSome].all id := by
  native_decide

/-- One DM date declaration read through the model reader, so the declared kind reaches the lowering
only as the reader leaves it. -/
private def readDate (id : FieldId) (name typeName formatKey format : String)
    (groupPath : GroupPath := ["Xf"]) (scope : List RepeatableLevel := []) (before1900 := false) :
    FlatFieldDecl :=
  let body := (formatKey, Lean.Json.str format) ::
    (if before1900 then [("youngerThan1900Check", Lean.Json.bool true)] else [])
  let fieldJson := Lean.Json.mkObj [("fieldType", Lean.Json.mkObj [("type", typeName),
    (typeName, Lean.Json.mkObj body)])]
  (readFieldType id groupPath name scope fieldJson).toOption.getD
    { id, groupPath, name, policy := { kind := .string } }

/- The measured pair of the [format-string checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-first-filled-reads-the-format-string):
a DATE and a DATE_FRAGMENT declared `yyyy` share one format and lower onto the one fragment carrier,
the declared kind consulted nowhere, while two complete dates spelled differently are two formats and
are refused beside their same-format control. -/
example :
    let model : FlatModel := { fields := [readDate 1 "YrDate" "DateType" "format" "yyyy",
      readDate 2 "YrFrag" "DateFragmentType" "formatOfFragment" "yyyy",
      readDate 3 "YrTarget" "DateType" "format" "yyyy",
      readDate 4 "Dotted" "DateType" "format" "dd.MM.yyyy",
      readDate 5 "Iso" "DateType" "format" "yyyy-MM-dd",
      readDate 6 "Target" "DateType" "format" "yyyy-MM-dd",
      readDate 7 "Iso2" "DateType" "format" "yyyy-MM-dd"] }
    let lowers (target operation : String) : Bool :=
      (lowerComputation model .english
        { group := ["Xf"], name := "C", targetRelPath := "../" ++ target, commonPrecondition := none
          alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption.isSome
    [model.fields.all (·.temporalTargetPolicy.isSome),
     lowers "YrTarget" "FirstFilledValue(YrDate, YrFrag)",
     !lowers "Target" "FirstFilledValue(Dotted, Iso)",
     lowers "Target" "FirstFilledValue(Iso, Iso2)"].all id := by
  native_decide

/- A temporal target's carrier is chosen by its profile, which the format decides, so a DATE declared
`HH:mm:ss` is a Time target and a TIME declared `yyyy-MM-dd` a full-Date one, at a fixed target and at
a row, as the [format-gate checkpoint](../../../docs/sources/repeatable-temporal-computation-probes.md#src-temporal-computed-target-gate-reads-format-not-kind)
measures the target gate. A DateFragment target carrying the pre-1900 check is the fragment
carrier's to refuse, not the full-Date carrier's. -/
example :
    let rows : List RepeatableGroupDecl :=
      [{ level := 10, path := ["Xf", "Rows"], repeatability := some 3 },
       { level := 20, path := ["Xf", "Rows", "Choices"], repeatability := some 3 },
       { level := 30, path := ["Xf", "Rows", "Tasks"], repeatability := some 3 }]
    let model : FlatModel := { repeatableGroups := rows, fields := [
      readDate 1 "ClockDate" "DateType" "format" "HH:mm:ss",
      readDate 2 "T1" "TimeType" "format" "HH:mm:ss",
      readDate 3 "T2" "TimeType" "format" "HH:mm:ss",
      readDate 4 "DayTime" "TimeType" "format" "yyyy-MM-dd",
      readDate 5 "D1" "DateType" "format" "yyyy-MM-dd",
      readDate 6 "D2" "DateType" "format" "yyyy-MM-dd",
      readDate 7 "CheckedYear" "DateFragmentType" "formatOfFragment" "yyyy" (before1900 := true),
      readDate 8 "Y1" "DateFragmentType" "formatOfFragment" "yyyy",
      readDate 9 "Y2" "DateFragmentType" "formatOfFragment" "yyyy",
      readDate 10 "Target" "DateType" "format" "HH:mm:ss" ["Xf", "Rows", "Tasks"] [10, 30],
      readDate 11 "Choice" "TimeType" "format" "HH:mm:ss" ["Xf", "Rows", "Choices"] [10, 20]] }
    let lowered (group : GroupPath) (target operation : String) : Lowering Unit :=
      (lowerComputation model .english
        { group, name := "C", targetRelPath := "../" ++ target, commonPrecondition := none
          alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).map
        fun _ => ()
    let refusedBy (carrier : String) : Lowering Unit → Bool
      | .error refusal => (refusal.detail.splitOn carrier).length > 1
      | .ok _ => false
    [model.fields.all (·.temporalTargetPolicy.isSome),
     (lowered ["Xf"] "ClockDate" "FirstFilledValue(T1, T2)").isOk,
     (lowered ["Xf"] "DayTime" "FirstFilledValue(D1, D2)").isOk,
     (lowered ["Xf", "Rows", "Tasks"] "Target" "FirstFilledValue(../Choices*/Choice)").isOk,
     refusedBy "DateFragmentFirstFilledComputationElabError"
       (lowered ["Xf"] "CheckedYear" "FirstFilledValue(Y1, Y2)")].all id := by
  native_decide

/- Analyze and Translate need authored operand order, including a literal written first. -/
example :
    let having (text : String) : Option SurfaceCorrelatedHaving :=
      match parseText .english text with
      | .ok parsed => (lowerHaving parsed.body).toOption
      | .error _ => none
    let field : AuthoredNumericExpr SurfaceHavingNumericAtom := .atom (.field
      { origin := .inner, field := { base := .relative 0, groups := ["Rows"], field := "V" } })
    [("<", SurfaceComparisonOp.less), ("<=", .lessEqual), (">", .greater),
     (">=", .greaterEqual), ("==", .equal), ("!=", .notEqual)].all (fun (text, op) =>
      having ("6 " ++ text ++ " [Rows/V]") ==
        some (.numeric op (.literal { value := 6, authoredScale := 0 }) field) &&
      having ("[Rows/V] " ++ text ++ " 6") ==
        some (.numeric op field (.literal { value := 6, authoredScale := 0 }))) := by
  native_decide

/- The reader keeps a literal's authored scale, a written trailing zero included, and its sign and
width, so the equality scale gate `HavingNumberLiteral` locks sees what the measured rows wrote. -/
example :
    let literal? (text : String) : Option (SurfaceComparisonOp × Rat × Int) :=
      match parseText .english text with
      | .ok parsed =>
          match lowerHaving parsed.body with
          | .ok (.numeric op _ (.literal literal))
          | .ok (.numeric op (.literal literal) _) => some (op, literal.value, literal.authoredScale)
          | _ => none
      | .error _ => none
    [literal? "[Rows/V] == 1.0" == some (.equal, 1, 1),
     literal? "[Rows/V] == 1.50" == some (.equal, 3 / 2, 2),
     literal? "1.5 == [Rows/V]" == some (.equal, 3 / 2, 1),
     literal? "1.5 > [Rows/V]" == some (.greater, 3 / 2, 1),
     literal? "[Rows/V] > -1" == some (.greater, -1, 0),
     literal? "[Rows/V] < 1234567890123456" == some (.less, 1234567890123456, 0)].all id := by
  native_decide

private def rangeModel : FlatModel :=
  let range (id : FieldId) (groupPath : GroupPath) (name : String) (scope : List RepeatableLevel) :
      FlatFieldDecl :=
    { id, groupPath, name, policy := { kind := .dateRange }, repeatableScope := scope
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }
  { fields := [range 1 ["Form"] "Fixed" [], range 2 ["Form", "Rows"] "Window" [10]]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

/- A DateRange `FirstFilledValue` over a star lowers onto the one starred carrier at a fixed target. -/
example :
    (lowerComputation rangeModel .english
      { group := ["Form"], name := "C", targetRelPath := "../Fixed", commonPrecondition := none
        alternatives := [{ precondition := none, operation := "FirstFilledValue(Rows*/Window)" }]
        errorCodesToSuppress := [] }).toOption.isSome := by
  native_decide

private def booleanModel : FlatModel :=
  let boolean (id : FieldId) (groupPath : GroupPath) (name : String) (scope : List RepeatableLevel) :
      FlatFieldDecl :=
    { id, groupPath, name, policy := { kind := .boolean }, repeatableScope := scope }
  { fields := [boolean 1 ["Form", "Rows", "Tasks"] "Target" [10, 30],
      boolean 2 ["Form", "Rows", "Choices"] "Choice" [10, 20]]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 },
      { level := 20, path := ["Form", "Rows", "Choices"], repeatability := some 3 },
      { level := 30, path := ["Form", "Rows", "Tasks"], repeatability := some 3 }] }

/- A Boolean `FirstFilledValue` lowers onto the one Boolean carrier over a sibling star at a row
target. -/
example :
    (lowerComputation booleanModel .english
      { group := ["Form", "Rows", "Tasks"], name := "C", targetRelPath := "../Target"
        commonPrecondition := none, errorCodesToSuppress := []
        alternatives := [{ precondition := none, operation := "FirstFilledValue(../Choices*/Choice)" }]
      }).toOption.isSome := by
  native_decide

private def customModel : FlatModel :=
  let custom (id : FieldId) (groupPath : GroupPath) (name : String) (scope : List RepeatableLevel) :
      FlatFieldDecl :=
    { id, groupPath, name, policy := { kind := .string }, repeatableScope := scope
      customType := some { name := "Code" } }
  { fields := [custom 1 ["Form"] "Fixed" [], custom 2 ["Form"] "First" [],
      custom 3 ["Form"] "Second" [], custom 4 ["Form", "Rows", "Tasks"] "Target" [10, 30],
      custom 5 ["Form", "Rows", "Choices"] "Choice" [10, 20]]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 },
      { level := 20, path := ["Form", "Rows", "Choices"], repeatability := some 3 },
      { level := 30, path := ["Form", "Rows", "Tasks"], repeatability := some 3 }] }

/- A Custom `FirstFilledValue` lowers onto the one Custom carrier, not the ordinary String one, over a
list at a fixed target and over a sibling star at a row target. -/
example :
    let computation (group : GroupPath) (target operation : String) : DmComputation :=
      { group, name := "C", targetRelPath := "../" ++ target, commonPrecondition := none
        alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
    [(lowerComputation customModel .english
        (computation ["Form"] "Fixed" "FirstFilledValue(First, Second)")).toOption.isSome,
     (lowerComputation customModel .english
        (computation ["Form", "Rows", "Tasks"] "Target" "FirstFilledValue(../Choices*/Choice)")).toOption.isSome].all id := by
  native_decide

private def fixedBooleanModel (kind : FieldKind := .boolean) : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Form"], name := "Flag", policy := { kind } },
      { id := 2, groupPath := ["Form"], name := "Copy", policy := { kind := .boolean } },
      { id := 3, groupPath := ["Form"], name := "Fallback", policy := { kind := .boolean } }] }

private def fixedBooleanDefinition (operation : String) : DmComputation :=
  { group := ["Form"], name := "FlagComp", targetRelPath := "../Flag"
    commonPrecondition := none, errorCodesToSuppress := []
    alternatives := [{ precondition := none, operation }] }

private def fixedBooleanRun (operation : String) (stored : Option String)
    (kind : FieldKind := .boolean) (dependent : Bool := false) : Option (List ComputedOutcome) := do
  let model := fixedBooleanModel kind
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let fields := stored.toList.map fun value => ("Flag", Lean.Json.str value)
  let input ← (readDocument dm (Lean.Json.mkObj [
    ("Form", Lean.Json.mkObj fields)])).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let (_, producer) ← (lowerComputation model .english (fixedBooleanDefinition operation)).toOption
  let steps ← if dependent then do
      let (_, copy) ← (lowerComputation model .english
        { (fixedBooleanDefinition "FirstFilledValue(Flag, Fallback)") with
          name := "CopyComp", targetRelPath := "../Copy" }).toOption
      pure [copy, producer]
    else pure [producer]
  (runComputations world prepared checked steps).toOption

example :
    fixedBooleanRun "True" (some "false") ==
      some [{ pointer := "Form/Flag", outcome := "value true" }] ∧
    fixedBooleanRun "False" (some "true") ==
      some [{ pointer := "Form/Flag", outcome := "value false" }] ∧
    fixedBooleanRun "True" (some "true") == some [] ∧
    fixedBooleanRun "False" (some "false") == some [] ∧
    fixedBooleanRun "True" none ==
      some [{ pointer := "Form/Flag", outcome := "value true" }] ∧
    fixedBooleanRun "True" (some "bad") ==
      some [{ pointer := "Form/Flag", outcome := "value true" }] ∧
    fixedBooleanRun "True" none .confirm ==
      some [{ pointer := "Form/Flag", outcome := "value true" }] ∧
    fixedBooleanRun "False" none .confirm == none := by
  native_decide

example :
    fixedBooleanRun "False" (some "true") .boolean true == some [
      { pointer := "Form/Flag", outcome := "value false" },
      { pointer := "Form/Copy", outcome := "value false" }] := by
  native_decide

example :
    let computation := fixedBooleanDefinition "True"
    let guarded := { computation with commonPrecondition := some "FieldFilled(Fallback)" }
    !(lowerComputation (fixedBooleanModel .string) .english computation).isOk ∧
      (lowerComputation fixedBooleanModel .english guarded).isOk ∧
      !(lowerComputation fixedBooleanModel .english
        { guarded with commonPrecondition := some "FieldFilled(Flag)" }).isOk := by
  native_decide

example :
    let computation : DmComputation := {
      group := ["Order"], name := "Self", targetRelPath := "../Amt"
      commonPrecondition := some "AllFieldsFilled(Ref, Amt)"
      alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }
    !(lowerComputation model .english computation).isOk := by native_decide

end A12Kernel.Dm.LowerLocks
