import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.PartialParallelRuleLocks
open Lean

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Et", "Rows"], repeatableScope := [9, 10], policy := { kind := .number { scale := 0, signed := false } } },
    { id := 2, name := "Note", groupPath := ["Et", "Rows"], repeatableScope := [9, 10], policy := { kind := .number { scale := 0, signed := false } } },
    { id := 3, name := "Key", groupPath := ["Et", "Side"], repeatableScope := [9, 20], policy := { kind := .number { scale := 0, signed := false } } },
    { id := 4, name := "Val", groupPath := ["Et", "Side"], repeatableScope := [9, 20], policy := { kind := .number { scale := 0, signed := false } } } ]
  repeatableGroups := [
    { level := 9, path := ["Et"], repeatability := some 5 },
    { level := 10, path := ["Et", "Rows"], repeatability := some 5, indexField := some 1 },
    { level := 20, path := ["Et", "Side"], repeatability := some 5, indexField := some 3 } ] }

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def rule (condition : String) : DmRule := {
  group := ["Et", "Rows"], name := "Parallel", errorCode := "PARALLEL", severity := "ERROR",
  errorEntityRelPath := "../Note", condition }

private def root (left right : List (String × String)) : Json :=
  .mkObj [
    ("Rows", .arr (left.map fun (key, value) => Json.mkObj [("Key", .str key), ("Note", .str value)]).toArray),
    ("Side", .arr (right.map fun (key, value) => Json.mkObj [("Key", .str key), ("Val", .str value)]).toArray)]

private def world : World := { now := { epochMillis := 0 } }

private abbrev Observation := List MessageRepetitionCoordinate × Polarity

private def execute (condition : String) (relevant : List RelevantEntityPattern)
    (emptyPayloads fixedRoot : Bool := false) (roots : Option (List Json) := none)
    (messageCache : Option MessageIndexCache := none) (extended : Bool := false)
    (errorTarget : Option String := none) (full : Bool := false)
    (expectedErrorField : Option FieldId := none) : Except String (List Observation) := do
  let selectedModel := if fixedRoot then
    { model with
      fields := model.fields.map fun field => { field with repeatableScope := field.repeatableScope.drop 1 }
      repeatableGroups := model.repeatableGroups.filter (·.level != 9) }
    else model
  let selectedModel := if extended then { selectedModel with fields := selectedModel.fields ++ [
    { id := 7, name := "Extra", groupPath := ["Et", "Rows"], repeatableScope := [9, 10],
      policy := { kind := .number { scale := 0, signed := false } } },
    { id := 8, name := "Extra", groupPath := ["Et", "Side"], repeatableScope := [9, 20],
      policy := { kind := .number { scale := 0, signed := false } } },
    { id := 9, name := "Limit", groupPath := ["Other"],
      policy := { kind := .number { scale := 0, signed := false } } }] } else selectedModel
  let selectedDm := { dm with flat := selectedModel }
  let left := if emptyPayloads then [("1", ""), ("2", "")] else [("1", "10"), ("2", "20")]
  let right := if emptyPayloads then [("1", ""), ("3", "")] else [("1", "30"), ("3", "40")]
  let outer := root left right
  let data := Json.mkObj ([("Et", if fixedRoot then outer else .arr ((roots.getD [outer]).toArray))] ++
    if extended then [("Other", .mkObj [("Limit", .str "5")])] else [])
  let input ← (readDocument selectedDm data).mapError reprStr
  if !input.refusals.isEmpty then throw (reprStr input.refusals)
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler selectedModel).mapError reprStr
  let checked ← (checkDocument prepared "en_US" input.data).mapError reprStr
  let sourceRule := { rule condition with errorEntityRelPath := errorTarget.getD "../Note" }
  let plan ← (checkParallelRule selectedDm .english sourceRule).mapError reprStr
  let messages ← if full then runValidationRule world checked (.parallel plan) messageCache
    else runPartialParallelRule checked plan relevant messageCache
  if let some field := expectedErrorField then
    if messages.any (·.errorAddress.field != field) then
      throw ("unexpected error fields: " ++ reprStr (messages.map (·.errorAddress.field)))
  pure (messages.map fun message => ((if fixedRoot then [.concrete 1] else []) ++ message.errorAddress.coordinates, message.messageType))

private def positive := "FieldFilled(/Et/Rows/Note) Or FieldFilled(/Et/Side/Val)"
private def collective := "FieldsNotCollectivelyFilled(/Et/Rows/Note, /Et/Side/Val)"
private def whole := [RelevantEntityPattern.allInstances ["Et"]]
private def field (side name : String) : RelevantEntityPattern :=
  RelevantEntityPattern.allInstances ["Et", side, name]
private def concreteField (side name : String) (row : Nat) : RelevantEntityPattern :=
  { path := ["Et", side, name], indices := [.concrete 1, .concrete row, .concrete 1] }
private def keys := [field "Rows" "Key", field "Side" "Key"]
private def payloads := [field "Rows" "Note", field "Side" "Val"]
private def leftKeyExcluded := [field "Rows" "Note", field "Side" "Key", field "Side" "Val"]
private def leftKeyOne := concreteField "Rows" "Key" 1 :: leftKeyExcluded
private def rightKeyOne := [field "Rows" "Key", field "Rows" "Note", field "Side" "Val",
  concreteField "Side" "Key" 1]
private def firstError := [field "Rows" "Key", field "Side" "Key", field "Side" "Val",
  concreteField "Rows" "Note" 1]
private def twoErrors := firstError ++ [concreteField "Rows" "Note" 2]
private def v (row : Nat) : Observation := ([.concrete 1, .concrete row], .value)
private def o (row : Nat) : Observation := ([.concrete 1, .concrete row], .omission)
private def vu : Observation := ([.concrete 1, .unknown], .value)
private def ou : Observation := ([.concrete 1, .unknown], .omission)

private def run (relevant : List RelevantEntityPattern) : Option (List (List MessageRepetitionCoordinate)) :=
  (execute positive relevant).toOption.map (List.map Prod.fst)

#guard run whole == some [[.concrete 1, .concrete 1], [.concrete 1, .concrete 2], [.concrete 1, .unknown]]
#guard run [] == some []
#guard run [{ path := ["Et", "Rows"], indices := [.concrete 1, .concrete 1] }] == some []
#guard run [{ path := ["Et", "Rows"], indices := [.concrete 1, .concrete 1] },
  { path := ["Et", "Rows"], indices := [.concrete 1, .concrete 2] }] ==
  some [[.concrete 1, .concrete 1], [.concrete 1, .concrete 2]]

-- The partial-parallel capture (2026-10-10) distinguishes duplicate unknown pointers;
-- eraseDups alone would lose this observable multiplicity.
private def check (name condition : String) (relevant : List RelevantEntityPattern)
    (expected : List Observation) (emptyPayloads fixedRoot : Bool := false)
    (roots : Option (List Json) := none) : Option (String × String) :=
  match execute condition relevant emptyPayloads fixedRoot roots with
  | .error error => some (name, error)
  | .ok actual =>
    if actual.length == expected.length && expected.eraseDups.all (fun entry =>
        (actual.filter (· == entry)).length == (expected.filter (· == entry)).length) then none
    else some (name, "expected " ++ reprStr expected ++ "; observed " ++ reprStr actual)

private def number (operator : String) := "[/Et/Rows/Note] " ++ operator ++ " [/Et/Side/Val]"
private def fill (operator : String) := operator ++ "(/Et/Rows/Note, /Et/Side/Val)"
private def guardedFill (operator : String) := "(" ++ number "==" ++ ") And " ++ fill operator

private def duplicateRoot := root [("1", "10"), ("1", "20")] [("1", "30")]

#guard (execute positive whole false false (some [duplicateRoot])).toOption == some [v 2]
#guard (execute positive whole false false (some [duplicateRoot])
  (some { insertions := [{ group := 10, parentPath := [1], key := .number 1, row := 1 }] })).toOption == some [v 1]
#guard match execute positive whole false false (some [duplicateRoot]) (some { insertions := [] }) with
  | .error reason => reason == (repr (ParallelPresenceRuleEvaluationError.join
      (.unresolvedDuplicatePointer 2 ["Et", "Rows"]))).pretty
  | .ok _ => false

private def outerFirst : List RelevantEntityPattern := [{ path := ["Et"], indices := [.concrete 1] }]
private def outerSecond : List RelevantEntityPattern := [{ path := ["Et"], indices := [.concrete 2] }]
private def parentObservation (parent : Nat) (row : MessageRepetitionCoordinate)
    (polarity : Polarity := .value) : Observation := ([.concrete parent, row], polarity)
private def matchedParents := [root [("1", "10")] [("1", "30")],
  root [("1", "20")] [("1", "40")]]
private def swappedParents := [root [("1", "10")] [("2", "30")],
  root [("2", "20")] [("1", "40")]]
private def mixedParents := [root [("1", ""), ("2", "20")] [("1", "30"), ("2", "40")],
  root [("1", ""), ("2", "")] [("1", "30"), ("2", "40")]]
private def parentErrorLeaves : List RelevantEntityPattern := keys ++ [field "Side" "Val",
  { path := ["Et", "Rows", "Note"], indices := [.concrete 1, .concrete 1, .concrete 1] },
  { path := ["Et", "Rows", "Note"], indices := [.concrete 2, .concrete 2, .concrete 1] }]
private def failures : List (String × String) := [
  check "payloads without keys" positive payloads [],
  check "keys without payloads" positive keys [],
  check "left group only" positive [RelevantEntityPattern.allInstances ["Et", "Rows"]] [v 1, v 2],
  check "left keys excluded" positive leftKeyExcluded [vu, vu],
  check "one left key" positive leftKeyOne [v 1, vu],
  check "one right key" positive rightKeyOne [v 1, v 2],
  check "far side only" positive [field "Side" "Key", field "Side" "Val"] [],
  check "matched key negative" "FieldNotFilled(/Et/Rows/Note) And FieldFilled(/Et/Side/Val)"
    leftKeyOne [],
  check "unmatched key negative" "FieldNotFilled(/Et/Rows/Note) And FieldFilled(/Et/Side/Val)"
    whole [ou],
  check "repeatable concrete error row" positive firstError [],
  check "repeatable wildcard error row" positive
    [field "Rows" "Key", field "Side" "Key", field "Side" "Val",
      { path := ["Et", "Rows", "Note"], indices := [.concrete 1, .all, .concrete 1] }]
    [v 1, v 2, vu],
  check "two error selectors permit dispatch" positive twoErrors [v 1, v 2, vu],
  check "two error selectors retain leaf membership" collective twoErrors [o 2],
  check "fixed root concrete error row" positive firstError [v 1, vu] false true,
  check "fixed root concrete group row" positive
    [{ path := ["Et", "Rows"], indices := [.concrete 1, .concrete 1] }] [v 1] false true,
  check "number equal" (number "==") whole [],
  check "number unequal" (number "!=") whole [v 1, o 2, ou],
  check "number less" (number "<") whole [v 1, ou],
  check "number less equal" (number "<=") whole [v 1, ou],
  check "number greater" (number ">") whole [o 2],
  check "number greater equal" (number ">=") whole [o 2],
  check "empty number equal" (number "==") whole [o 1, o 2, ou] true,
  check "empty number less equal" (number "<=") whole [o 1, o 2, ou] true,
  check "empty number greater equal" (number ">=") whole [o 1, o 2, ou] true,
  check "all fields filled" (fill "AllFieldsFilled") whole [v 1],
  check "at least one field filled" (fill "AtLeastOneFieldFilled") whole [v 1, v 2, vu],
  check "more than one field filled" (fill "MoreThanOneFieldFilled") whole [v 1],
  check "not collectively filled" collective whole [o 2, ou],
  check "no field filled positive twin" (guardedFill "NoFieldFilled") whole [],
  check "not all filled positive twin" (guardedFill "NotAllFieldsFilled") whole [],
  check "not exactly one filled positive twin" (guardedFill "NotExactlyOneFieldFilled") whole [],
  check "no field filled empty" (guardedFill "NoFieldFilled") whole [o 1, o 2, ou] true,
  check "not all filled empty" (guardedFill "NotAllFieldsFilled") whole [o 1, o 2, ou] true,
  check "not exactly one filled empty" (guardedFill "NotExactlyOneFieldFilled") whole [o 1, o 2, ou] true,
  check "one admitted left key empty comparison" (number "==") leftKeyOne [o 1] true,
  check "one admitted left key empty fill" (guardedFill "NoFieldFilled") leftKeyOne [o 1] true
  , check "all concrete left index rows remain non-universal" collective
    [concreteField "Rows" "Key" 1, concreteField "Rows" "Key" 2,
      field "Rows" "Note", field "Side" "Key", field "Side" "Val"] [o 2]
  , check "all concrete right index rows remain non-universal" collective
    [field "Rows" "Key", field "Rows" "Note", concreteField "Side" "Key" 1,
      concreteField "Side" "Key" 2, field "Side" "Val"] [ou]
  , check "left group content" "GroupFilled(/Et/Rows) And FieldFilled(/Et/Side/Val)" whole [v 1]
  , check "right group content" "FieldFilled(/Et/Rows/Note) And GroupFilled(/Et/Side)" whole [v 1]
  , check "both group content" "GroupFilled(/Et/Rows) And GroupFilled(/Et/Side)" whole [v 1]
  , check "missing left group" "GroupNotFilled(/Et/Rows) And FieldFilled(/Et/Side/Val)" whole [ou]
  , check "missing right group" "FieldFilled(/Et/Rows/Note) And GroupNotFilled(/Et/Side)" whole [o 2]
  , check "left group empty payloads" "GroupFilled(/Et/Rows) Or FieldFilled(/Et/Side/Val)"
      whole [v 1, v 2] true
  , check "left group excludes unknown key" "GroupFilled(/Et/Rows) Or FieldFilled(/Et/Side/Val)"
      leftKeyOne [v 1, vu]
  , check "missing group excluded column" "GroupNotFilled(/Et/Rows) And FieldFilled(/Et/Side/Val)"
      leftKeyExcluded []
  , check "duplicate four outers whole" positive whole [v 2] false false
      (some (duplicateRoot :: List.replicate 3 (Json.mkObj [])))
  , check "duplicate five outers whole" positive whole [v 1] false false
      (some (duplicateRoot :: List.replicate 4 (Json.mkObj [])))
  , check "duplicate five outers partial first" positive outerFirst [v 2] false false
      (some (duplicateRoot :: List.replicate 4 (Json.mkObj [])))
  , check "duplicate first key only" positive leftKeyOne [v 1] false false (some [duplicateRoot])
  , check "number key aliases" positive whole [v 1] false false
      (some [root [("1.0", "10")] [("1", "30")]])
  , check "missing left group covered by fields" "GroupNotFilled(/Et/Rows) And FieldFilled(/Et/Side/Val)"
      (keys ++ payloads) [ou]
  , check "missing right group covered by fields" "FieldFilled(/Et/Rows/Note) And GroupNotFilled(/Et/Side)"
      (keys ++ payloads) [o 2]
  , check "same keys remain in separate parents" positive whole
      [v 1, parentObservation 2 (.concrete 1)] false false (some matchedParents)
  , check "second parent selection" positive outerSecond
      [parentObservation 2 (.concrete 1)] false false (some matchedParents)
  , check "swapped parent keys never cross join"
      "FieldFilled(/Et/Rows/Note) And FieldFilled(/Et/Side/Val)" whole [] false false
      (some swappedParents)
  , check "swapped parent keys retain local unknown pointers" positive whole
      [v 1, vu, parentObservation 2 (.concrete 1), parentObservation 2 .unknown]
      false false (some swappedParents)
  , check "reversed parents retain local unknown pointers" positive outerSecond
      [parentObservation 2 (.concrete 1), parentObservation 2 .unknown]
      false false (some swappedParents.reverse)
  , check "parent selector union dispatches both parents" positive parentErrorLeaves
      [v 1, v 2, parentObservation 2 (.concrete 1), parentObservation 2 (.concrete 2)]
      false false (some mixedParents)
  , check "parent selector union retains original payload leaves" collective parentErrorLeaves
      [o 1, parentObservation 2 (.concrete 2) .omission] false false (some mixedParents)
  ].filterMap id

#guard failures.isEmpty

private def framedModel (capacity : Nat) : FlatModel := { model with
    fields := model.fields.map fun field =>
      if field.groupPath == ["Et", "Rows"] then
        { field with groupPath := ["Et", "Frame", "Rows"] }
      else { field with repeatableScope := [20] }
    repeatableGroups := model.repeatableGroups.map fun group =>
      if group.level == 9 then { group with path := ["Et", "Frame"], repeatability := some capacity }
      else if group.level == 10 then { group with path := ["Et", "Frame", "Rows"] } else group }

private def framed (capacity : Nat) (full : Bool) : Except String (List Observation) := do
  let selectedModel := framedModel capacity
  let selectedDm := { dm with flat := selectedModel }
  let data := Json.mkObj [("Et", .mkObj [
    ("Frame", .arr #[.mkObj [("Rows", .arr #[.mkObj [("Key", .str "1"), ("Note", .str "10")]])],
      .mkObj [("Rows", .arr #[.mkObj [("Key", .str "2"), ("Note", .str "20")]])]]),
    ("Side", .arr #[.mkObj [("Key", .str "1"), ("Val", .str "30")],
      .mkObj [("Key", .str "3"), ("Val", .str "40")]])])]
  let input ← (readDocument selectedDm data).mapError reprStr
  if !input.refusals.isEmpty then throw (reprStr input.refusals)
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler selectedModel).mapError reprStr
  let checked ← (checkDocument prepared "en_US" input.data).mapError reprStr
  let plan ← (checkParallelRule selectedDm .english
    { (rule "[/Et/Frame/Rows/Note] < [/Et/Side/Val]") with group := ["Et", "Frame", "Rows"] }).mapError reprStr
  let messages ← if full then runValidationRule world checked (.parallel plan)
    else runPartialParallelRule checked plan whole
  pure (messages.map fun m => (m.errorAddress.coordinates, m.messageType))

private def framedExpected : List Observation := [v 1, ou,
  ([.concrete 2, .unknown], .omission), ([.concrete 2, .unknown], .omission)]
#guard (framed 3 false).toOption == some (framedExpected ++
  [([.concrete 3, .unknown], .omission), ([.concrete 3, .unknown], .omission)])
#guard (framed 3 true).toOption == some (framedExpected ++
  [([.concrete 3, .unknown], .omission), ([.concrete 3, .unknown], .omission)])
#guard (framed 6 false).toOption == some framedExpected
#guard (framed 6 true).toOption == some framedExpected

private def framedErrorAdmission (error : String) : Except String Unit := do
  let base := framedModel 2
  let selectedDm := { dm with flat := { base with fields := base.fields ++ [
    { id := 5, name := "Notice", groupPath := ["Et", "Report"], policy := { kind := .string } },
    { id := 6, name := "Notice", groupPath := ["Et", "Report", "Detail"], policy := { kind := .string } }] } }
  let _ ← (checkValidationRule selectedDm .english {
    (rule "GroupFilled(/Et) And FieldFilled(/Et/Frame/Rows/Note) And FieldFilled(/Et/Side/Val)") with
    group := ["Et"], errorEntityRelPath := error }).mapError (·.detail)
  pure ()

#guard (framedErrorAdmission "/Et/Frame/Rows/Note").isOk
#guard ["/Et/Report/Notice", "/Et/Report/Detail/Notice"].all fun target =>
  match framedErrorAdmission target with
  | .error reason => reason == "MVK_NO_WILDCARD"
  | .ok _ => false

private def richRoot (extra : String := "1") (leftExtra : String := "3") : Json := .mkObj [
  ("Rows", .arr #[.mkObj [("Key", .str "1"), ("Note", .str "2"), ("Extra", .str leftExtra)]]),
  ("Side", .arr #[.mkObj [("Key", .str "1"), ("Val", .str "4"), ("Extra", .str extra)]])]

private def rich (condition : String) (extra : String := "1") (full : Bool := false) : Option (List Observation) :=
  (execute condition (whole ++ [RelevantEntityPattern.allInstances ["Other"]]) false false
    (some [richRoot extra]) none true none full).toOption

private def richComparison := "[/Et/Rows/Note] + [/Et/Rows/Extra] == [/Et/Side/Val] + [/Et/Side/Extra]"
#guard [false, true].all fun full =>
  rich richComparison "1" full == some [v 1] &&
  rich richComparison "2" full == some [] &&
  rich "[/Et/Rows/Note] + [/Et/Rows/Extra] == [/Other/Limit] And FieldFilled(/Et/Side/Val)" "1" full == some [v 1]

#guard [false, true].all fun full =>
  (execute "FieldFilled(/Et/Rows/Note) And FieldNotFilled(/Et/Rows/Extra) And FieldFilled(/Et/Side/Val)"
    whole (roots := some [richRoot "1" ""]) (extended := true) (full := full)).toOption == some [o 1] &&
  rich "FieldFilled(/Et/Rows/Note) And FieldFilled(/Et/Side/Val) And FieldNotFilled(/Et/Side/Extra)"
    "" full == some [o 1]

#guard [false, true].all fun full =>
  (execute richComparison whole (roots := some [richRoot]) (extended := true)
    (errorTarget := some "/Et/Rows/Extra") (full := full) (expectedErrorField := some 7)).toOption == some [v 1]

#guard [false, true].all fun full =>
  rich richComparison "bad" full == some [] &&
  rich ("(" ++ richComparison ++ ") Or FieldFilled(/Et/Rows/Note)") "bad" full == some [v 1]

#guard rich richComparison == some [v 1] &&
  (execute richComparison (keys ++ payloads ++ [field "Rows" "Extra"])
    (roots := some [richRoot]) (extended := true)).toOption == some []

#guard [false, true].all fun full =>
  (execute richComparison whole (roots := some [richRoot "2", richRoot])
    (extended := true) (full := full)).toOption == some [parentObservation 2 (.concrete 1)]

private def negativeJoined := "FieldNotFilled(/Et/Rows/Note) And FieldNotFilled(/Et/Side/Val)"
#guard !(execute ("FieldFilled(/Other/Limit) And " ++ negativeJoined) whole
    (roots := some [richRoot]) (extended := true)).isOk &&
  (execute ("FieldFilled(/Other/Limit) And FieldFilled(/Et/Rows/Extra) And " ++ negativeJoined) whole
    (roots := some [richRoot]) (extended := true)).isOk

private def frameGuardAdmission (guard : String) : Bool :=
  (checkParallelRule { dm with flat := framedModel 2 } .english {
    (rule (guard ++ " And FieldNotFilled(/Et/Frame/Rows/Note) And FieldFilled(/Et/Side/Val)")) with
    group := ["Et"], errorEntityRelPath := "/Et/Frame/Rows/Note" }).isOk

#guard !frameGuardAdmission "2 + 3 == 5" &&
  frameGuardAdmission "FieldFilled(/Et/Frame/Rows/Note)"

#guard !(checkParallelFieldRule model 2 4 2
  (.and (.leaf (.presence .left .filled)) (.leaf (.presence (.field {
    id := 99, name := "Note", groupPath := ["Et", "Rows"], repeatableScope := [9, 10],
    policy := { kind := .number { scale := 0, signed := false } } }) .filled)))
  "P" .error { parts := [] }).isOk

#guard !(execute "[/Et/Rows/Note] == 0 And FieldNotFilled(/Et/Side/Val)" whole).isOk &&
  (execute "[/Et/Rows/Note] != 0 And FieldNotFilled(/Et/Side/Val)" whole).isOk &&
  (execute "[/Et/Rows/Note] + 0 == 0 And FieldNotFilled(/Et/Side/Val)" whole).isOk

#guard !(execute "Abs([/Et/Rows/Note]) == 0 And FieldNotFilled(/Et/Side/Val)" whole).isOk &&
  (execute "Abs([/Et/Rows/Note]) == 1 And FieldNotFilled(/Et/Side/Val)" whole).isOk &&
  !(execute "Abs([/Et/Rows/Note] + [/Other/Limit]) == 1 And FieldNotFilled(/Et/Side/Val)"
    whole (roots := some [richRoot]) (extended := true)).isOk

private def mixedFillAdmission (operator : String) (reverse rescue : Bool := false) : Bool :=
  let operands := if reverse then "/Other/Limit, /Et/Rows/Note" else "/Et/Rows/Note, /Other/Limit"
  let condition := operator ++ "(" ++ operands ++ ") And FieldNotFilled(/Et/Side/Val)" ++
    if rescue then " And FieldFilled(/Et/Rows/Note)" else ""
  (execute condition whole (roots := some [richRoot]) (extended := true)).isOk

#guard ["AtLeastOneFieldFilled", "FieldsNotCollectivelyFilled"].all fun operator =>
  [false, true].all fun reverse =>
    !mixedFillAdmission operator reverse && mixedFillAdmission operator reverse true
#guard mixedFillAdmission "AllFieldsFilled" && mixedFillAdmission "AllFieldsFilled" true
#guard ["AtLeastOneFieldFilled", "FieldsNotCollectivelyFilled"].all fun operator =>
  (execute (operator ++ "(/Et/Rows/Note, /Et/Side/Val) And FieldNotFilled(/Et/Side/Val)") whole).isOk

end A12Kernel.Dm.PartialParallelRuleLocks
