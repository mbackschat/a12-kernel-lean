import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Parser

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

/- A count compared with a fractional threshold is refused, where the carrier would read `1.5` as an
integral literal. -/
example :
    [admitted "NumberOfFilledFields(Head) < 2", !admitted "NumberOfFilledFields(Head) < 1.5"].all id := by
  native_decide

/- `NumberOfDifferentValues` reaches the String/Enumeration and temporal carriers once the Number one
refuses its list, a star-free group operand included, which lowers to the scalar surface first; a
list mixing the families stays refused, and so does a plain second-root read, which the entity-list
carrier must not answer for the scalar carriers that refuse it. -/
example :
    [admitted "NumberOfDifferentValues(Ref, Head/Code) == 1", admitted "NumberOfDifferentValues(Rows*/Note) > 1",
     admitted "NumberOfDifferentValues(Head) > 0", admitted "NumberOfDifferentValues(Due1, Due2) == 1",
     !admitted "NumberOfDifferentValues(Ref, Due1) == 1", !admitted "[/Other/O] + [Amt] < 5"].all id := by
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

private def rowModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Order", "Rows"], name := "Due", policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" }, repeatableScope := [10] },
      { id := 2, groupPath := ["Order", "Rows"], name := "Flag", policy := { kind := .boolean }, repeatableScope := [10] },
      { id := 3, groupPath := ["Order", "Rows"], name := "Amt", policy := { kind := .number { scale := 0, signed := true } },
        repeatableScope := [10] },
      { id := 4, groupPath := ["Order", "Rows"], name := "Text", policy := { kind := .string }, repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Order", "Rows"], repeatability := some 5 }] }

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

/- A comparison reading no entity list is the scalar carriers' alone, so a second root's field is
refused with their reason rather than the entity carrier's. -/
example :
    (match parseText .english "[/Other/O] + [Amt] < 5" with
      | .ok parsed => match lowerCondition model ["Order"] false parsed.body with
        | .error refusal => refusal.detail.startsWith "A12Kernel.NumericValidationElabError.fieldOutsideRowGroup"
        | .ok _ => false
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

end A12Kernel.Dm.LowerLocks
