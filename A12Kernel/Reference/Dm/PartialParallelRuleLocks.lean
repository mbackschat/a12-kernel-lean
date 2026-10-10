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
    (messageCache : Option MessageIndexCache := none) : Except String (List Observation) := do
  let selectedModel := if fixedRoot then
    { model with
      fields := model.fields.map fun field => { field with repeatableScope := field.repeatableScope.drop 1 }
      repeatableGroups := model.repeatableGroups.filter (·.level != 9) }
    else model
  let selectedDm := { dm with flat := selectedModel }
  let left := if emptyPayloads then [("1", ""), ("2", "")] else [("1", "10"), ("2", "20")]
  let right := if emptyPayloads then [("1", ""), ("3", "")] else [("1", "30"), ("3", "40")]
  let outer := root left right
  let data := Json.mkObj [("Et", if fixedRoot then outer else .arr ((roots.getD [outer]).toArray))]
  let input ← (readDocument selectedDm data).mapError reprStr
  if !input.refusals.isEmpty then throw (reprStr input.refusals)
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler selectedModel).mapError reprStr
  let checked ← (checkDocument prepared "en_US" input.data).mapError reprStr
  let plan ← (checkParallelRule selectedDm .english (rule condition)).mapError reprStr
  let messages ← runPartialParallelRule checked plan relevant messageCache
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
  ].filterMap id

#guard failures.isEmpty

private def framed (capacity : Nat) (full : Bool) : Except String (List Observation) := do
  let selectedModel := { model with
    fields := model.fields.map fun field =>
      if field.groupPath == ["Et", "Rows"] then
        { field with groupPath := ["Et", "Frame", "Rows"] }
      else { field with repeatableScope := [20] }
    repeatableGroups := model.repeatableGroups.map fun group =>
      if group.level == 9 then { group with path := ["Et", "Frame"], repeatability := some capacity }
      else if group.level == 10 then { group with path := ["Et", "Frame", "Rows"] } else group }
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

end A12Kernel.Dm.PartialParallelRuleLocks
