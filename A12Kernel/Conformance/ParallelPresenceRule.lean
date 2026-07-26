import A12Kernel.Elaboration.ParallelPresenceRule

/-! # Bounded parallel presence-rule locks -/

namespace A12Kernel.Conformance.ParallelPresenceRule

open A12Kernel

private def indexDecl (id : FieldId) (group : String)
    (scope : RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := ["Order", group]
  name := "Department"
  policy := { kind := .string }
  repeatableScope := [scope]
}

private def targetDecl (id : FieldId) (group : String)
    (scope : RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := ["Order", group]
  name := "Headcount"
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := [scope]
}

private def demand : RepeatableGroupDecl := {
  level := 10
  path := ["Order", "Demand"]
  repeatability := some 3
  indexField := some 1
}

private def supply : RepeatableGroupDecl := {
  level := 20
  path := ["Order", "Supply"]
  repeatability := some 3
  indexField := some 3
}

private def model : FlatModel := {
  fields := [
    indexDecl 1 "Demand" 10, targetDecl 2 "Demand" 10,
    indexDecl 3 "Supply" 20, targetDecl 4 "Supply" 20,
    {
      id := 5
      groupPath := ["Order"]
      name := "Outside"
      policy := { kind := .string }
    }
  ]
  repeatableGroups := [demand, supply]
}

private def row (group coordinate : Nat) : RowAddr :=
  { group, path := [coordinate] }

private def cell (field coordinate : Nat) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [coordinate] }
  stored
  raw
}

private def data : DocumentData := {
  instantiatedRows := [
    row 10 1, row 10 2, row 20 1, row 20 2
  ]
  cells := [
    cell 1 1 "Zulu" (.parsed (.str "Zulu")),
    cell 2 1 "7" (.parsed (.num 7)),
    cell 1 2 "Alpha" (.parsed (.str "Alpha")),
    cell 2 2 "3" (.parsed (.num 3)),
    cell 3 1 "Alpha" (.parsed (.str "Alpha")),
    cell 4 1 "8" (.parsed (.num 8)),
    cell 3 2 "Beta" (.parsed (.str "Beta")),
    cell 4 2 "2" (.parsed (.num 2))
  ]
}

private def invalidSupplyData : DocumentData := {
  data with
    instantiatedRows := data.instantiatedRows ++ [row 20 3]
    cells := data.cells ++ [cell 4 3 "4" (.parsed (.num 4))]
}

private def invalidDemandData : DocumentData := {
  data with
    instantiatedRows := data.instantiatedRows ++ [row 10 3]
    cells := data.cells ++ [cell 2 3 "4" (.parsed (.num 4))]
}

private def world : World := { now := { epochMillis := 0 } }

private def preliminaryFor (source : DocumentData) :
    Option (CheckedIndexPreliminary model) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" source).toOption
  checked.applyFullIndexPreliminary.toOption

private def messagePlan : MessageRenderPlan :=
  { parts := [.text "parallel"] }

private def checkedRule? (errorField : FieldId) :
    Option (CheckedParallelPresenceRule model) :=
  (checkParallelPresenceRule model 2 4 errorField "PI" .error
    messagePlan).toOption

/- Static construction requires the emitted error field to be one of the two positive operands. -/
example :
    (match checkParallelPresenceRule model 2 4 5 "PI" .error
        messagePlan with
      | .error error => some error
      | .ok _ => none) =
      some (.errorFieldNotOperand 5 2 4) := by
  native_decide

/- Two fields in one keyed group remain ordinary iteration; they cannot manufacture a parallel plan. -/
example :
    (match checkParallelPresenceRule model 1 2 2 "PI" .error
        messagePlan with
      | .error error => some error
      | .ok _ => none) =
      some (.join (.incompatibleGroups demand.path demand.path)) := by
  native_decide

/- Every operand needs one indexed repeatable owner; a field merely sharing the rule's nonrepeatable ancestor cannot enter the join. -/
example :
    (match checkParallelPresenceRule model 2 5 2 "PI" .error
        messagePlan with
      | .error error => some error
      | .ok _ => none) =
      some (.missingIndexedOperandGroup 5) := by
  native_decide

private def evaluated? (errorField : FieldId) (source : DocumentData) :
    Option (List ParallelRuleRowOutcome) := do
  let preliminary ← preliminaryFor source
  let rule ← checkedRule? errorField
  (rule.evalFull preliminary).toOption

private def fired (field : FieldId) (path : List Nat) :
    FlatRuleOutcome :=
  .fired {
    errorAddress := { field, path }
    errorCode := "PI"
    severity := .error
    messageType := .value
    text := { text := "parallel" }
  }

/- The whole-rule scan follows lexical join-key order rather than either physical row order, and both clean unmatched directions remain ordinary nonfiring. -/
example : (evaluated? 2 data).map (·.map fun row => (row.key, row.outcome)) =
    some [
      (.text "Alpha", fired 2 [2]),
      (.text "Beta", .notFired),
      (.text "Zulu", .notFired)
    ] := by
  native_decide

/- The same condition can report on the other physical side without changing the join or condition order. -/
example : (evaluated? 4 data).map (·.map fun row => (row.key, row.outcome)) =
    some [
      (.text "Alpha", fired 4 [1]),
      (.text "Beta", .notFired),
      (.text "Zulu", .notFired)
    ] := by
  native_decide

/- A matched read stays definite in an invalid sibling column; only an unmatched read from that column is UNKNOWN. -/
example :
    (evaluated? 2 invalidSupplyData).map
      (·.map fun row => (row.key, row.outcome)) =
    some [
      (.text "Alpha", fired 2 [2]),
      (.text "Beta", .notFired),
      (.text "Zulu", .unknown)
    ] := by
  native_decide

/- Invalid-unmatched UNKNOWN is symmetric: it is not fabricated as an empty cell when the error target belongs to the clean side. -/
example :
    (evaluated? 4 invalidDemandData).map
      (·.map fun row => (row.key, row.outcome)) =
    some [
      (.text "Alpha", fired 4 [1]),
      (.text "Beta", .unknown),
      (.text "Zulu", .notFired)
    ] := by
  native_decide

/- A field outside both joined groups is structural misuse, never semantic UNKNOWN. -/
example : (preliminaryFor data).bind (fun preliminary =>
    (preliminary.resolveParallelIndexJoin demand supply).toOption.bind fun join =>
      join.rows.head?.bind fun first =>
        match first.readValidation preliminary 5 with
        | .error error => some error
        | .ok _ => none) =
    some (.fieldOutsideParallelGroups 5 demand.path supply.path) := by
  native_decide

private def wrappedIndexDecl (id : FieldId) (groupPath : GroupPath)
    (scope : RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath
  name := "Department"
  policy := { kind := .string }
  repeatableScope := [scope]
}

private def wrappedTargetDecl (id : FieldId) (groupPath : GroupPath)
    (scope : RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath
  name := "Headcount"
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := [scope]
}

private def wrappedDemand : RepeatableGroupDecl := {
  level := 30
  path := ["Plan", "W1", "Demand"]
  repeatability := some 3
  indexField := some 11
}

private def wrappedSupply : RepeatableGroupDecl := {
  level := 40
  path := ["Plan", "W2", "Inner", "Supply"]
  repeatability := some 3
  indexField := some 13
}

private def wrappedModel : FlatModel := {
  fields := [
    wrappedIndexDecl 11 wrappedDemand.path 30,
    wrappedTargetDecl 12 (wrappedDemand.path ++ ["Leaf"]) 30,
    wrappedIndexDecl 13 wrappedSupply.path 40,
    wrappedTargetDecl 14
      (wrappedSupply.path ++ ["Payload", "Leaf"]) 40
  ]
  repeatableGroups := [wrappedDemand, wrappedSupply]
}

private def wrappedCell (field coordinate : Nat) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [coordinate] }
  stored
  raw
}

private def wrappedData : DocumentData := {
  instantiatedRows := [
    row 30 1, row 30 2, row 40 1, row 40 2
  ]
  cells := [
    wrappedCell 11 1 "Zulu" (.parsed (.str "Zulu")),
    wrappedCell 12 1 "7" (.parsed (.num 7)),
    wrappedCell 11 2 "Alpha" (.parsed (.str "Alpha")),
    wrappedCell 12 2 "3" (.parsed (.num 3)),
    wrappedCell 13 1 "Alpha" (.parsed (.str "Alpha")),
    wrappedCell 14 1 "8" (.parsed (.num 8)),
    wrappedCell 13 2 "Beta" (.parsed (.str "Beta")),
    wrappedCell 14 2 "2" (.parsed (.num 2))
  ]
}

private def invalidWrappedSupplyData : DocumentData := {
  wrappedData with
    instantiatedRows := wrappedData.instantiatedRows ++ [row 40 3]
    cells := wrappedData.cells ++
      [wrappedCell 14 3 "4" (.parsed (.num 4))]
}

private def wrappedPreliminaryFor (source : DocumentData) :
    Option (CheckedIndexPreliminary wrappedModel) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler wrappedModel).toOption
  let checked ← (checkDocument prepared "en_US" source).toOption
  checked.applyFullIndexPreliminary.toOption

private def wrappedRule? (errorField : FieldId) :
    Option (CheckedParallelPresenceRule wrappedModel) :=
  (checkParallelPresenceRule wrappedModel 12 14 errorField "WPI" .error
    messagePlan).toOption

private def wrappedEvaluated? (errorField : FieldId)
    (source : DocumentData) : Option (List ParallelRuleRowOutcome) := do
  let preliminary ← wrappedPreliminaryFor source
  let rule ← wrappedRule? errorField
  (rule.evalFull preliminary).toOption

private def wrappedFired (field : FieldId) (path : List Nat) :
    FlatRuleOutcome :=
  .fired {
    errorAddress := { field, path }
    errorCode := "WPI"
    severity := .error
    messageType := .value
    text := { text := "parallel" }
  }

/- Nonrepeatable wrappers before both keyed groups and below both positive operands are transparent; only repeatable coordinates enter the physical address. -/
example :
    (wrappedEvaluated? 12 wrappedData).map
      (·.map fun result => (result.key, result.outcome)) =
    some [
      (.text "Alpha", wrappedFired 12 [2]),
      (.text "Beta", .notFired),
      (.text "Zulu", .notFired)
    ] := by
  native_decide

/- Asymmetric wrapper depth does not change which matched physical side owns the error address. -/
example :
    (wrappedEvaluated? 14 wrappedData).map
      (·.map fun result => (result.key, result.outcome)) =
    some [
      (.text "Alpha", wrappedFired 14 [1]),
      (.text "Beta", .notFired),
      (.text "Zulu", .notFired)
    ] := by
  native_decide

/- A wrapped invalid column still affects only an unmatched read; the matched row remains definite. -/
example :
    (wrappedEvaluated? 12 invalidWrappedSupplyData).map
      (·.map fun result => (result.key, result.outcome)) =
    some [
      (.text "Alpha", wrappedFired 12 [2]),
      (.text "Beta", .notFired),
      (.text "Zulu", .unknown)
    ] := by
  native_decide

private def frame : RepeatableGroupDecl := {
  level := 50
  path := ["Plan", "Frame"]
  repeatability := some 2
}

private def framedDemand : RepeatableGroupDecl := {
  level := 60
  path := ["Plan", "Frame", "Demand"]
  repeatability := some 3
  indexField := some 21
}

private def framedSupply : RepeatableGroupDecl := {
  level := 70
  path := ["Plan", "Supply"]
  repeatability := some 3
  indexField := some 23
}

private def framedModel : FlatModel := {
  fields := [
    {
      (wrappedIndexDecl 21 framedDemand.path 60) with
        repeatableScope := [50, 60]
    },
    {
      (wrappedTargetDecl 22 framedDemand.path 60) with
        repeatableScope := [50, 60]
    },
    wrappedIndexDecl 23 framedSupply.path 70,
    wrappedTargetDecl 24 framedSupply.path 70
  ]
  repeatableGroups := [frame, framedDemand, framedSupply]
}

private def framedRow (group : RepeatableLevel)
    (path : List Nat) : RowAddr := {
  group
  path
}

private def framedCell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw
}

private def framedData : DocumentData := {
  instantiatedRows := [
    framedRow 50 [1],
    framedRow 60 [1, 1],
    framedRow 60 [1, 2],
    framedRow 50 [2],
    framedRow 60 [2, 1],
    framedRow 60 [2, 2],
    framedRow 70 [1],
    framedRow 70 [2],
    framedRow 70 [3]
  ]
  cells := [
    framedCell 21 [1, 1] "Sales" (.parsed (.str "Sales")),
    framedCell 22 [1, 1] "9" (.parsed (.num 9)),
    framedCell 21 [1, 2] "Engineering"
      (.parsed (.str "Engineering")),
    framedCell 22 [1, 2] "3" (.parsed (.num 3)),
    framedCell 21 [2, 1] "Sales" (.parsed (.str "Sales")),
    framedCell 22 [2, 1] "1" (.parsed (.num 1)),
    framedCell 21 [2, 2] "Operations"
      (.parsed (.str "Operations")),
    framedCell 22 [2, 2] "4" (.parsed (.num 4)),
    framedCell 23 [1] "Sales" (.parsed (.str "Sales")),
    framedCell 24 [1] "5" (.parsed (.num 5)),
    framedCell 23 [2] "Operations"
      (.parsed (.str "Operations")),
    framedCell 24 [2] "2" (.parsed (.num 2)),
    framedCell 23 [3] "Legal" (.parsed (.str "Legal")),
    framedCell 24 [3] "1" (.parsed (.num 1))
  ]
}

private def invalidSecondFrameData : DocumentData := {
  framedData with
    instantiatedRows :=
      framedData.instantiatedRows ++ [framedRow 60 [2, 3]]
    cells := framedData.cells ++
      [framedCell 22 [2, 3] "6" (.parsed (.num 6))]
}

private def overLimitFrameData : DocumentData := {
  framedData with
    instantiatedRows :=
      framedData.instantiatedRows ++
        [framedRow 50 [3], framedRow 60 [3, 1]]
    cells := framedData.cells ++ [
      framedCell 21 [3, 1] "Sales" (.parsed (.str "Sales")),
      framedCell 22 [3, 1] "8" (.parsed (.num 8))
    ]
}

private def framedPreliminaryFor (source : DocumentData) :
    Option (CheckedIndexPreliminary framedModel) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler framedModel).toOption
  let checked ← (checkDocument prepared "en_US" source).toOption
  checked.applyFullIndexPreliminary.toOption

private def framedRule? :
    Option (CheckedParallelPresenceRule framedModel) :=
  (checkParallelPresenceRule framedModel 22 24 22 "FPI" .error
    messagePlan).toOption

private def rightFramedRule? :
    Option (CheckedParallelPresenceRule framedModel) :=
  (checkParallelPresenceRule framedModel 24 22 22 "FPI" .error
    messagePlan).toOption

private def framedEvaluated? (source : DocumentData) :
    Option (List ParallelRuleRowOutcome) := do
  let preliminary ← framedPreliminaryFor source
  let rule ← framedRule?
  (rule.evalFull preliminary).toOption

private def rightFramedEvaluated? (source : DocumentData) :
    Option (List ParallelRuleRowOutcome) := do
  let preliminary ← framedPreliminaryFor source
  let rule ← rightFramedRule?
  (rule.evalFull preliminary).toOption

private def framedFired (path : List Nat) : FlatRuleOutcome :=
  .fired {
    errorAddress := { field := 22, path }
    errorCode := "FPI"
    severity := .error
    messageType := .value
    text := { text := "parallel" }
  }

/- A repeatable non-indexed ancestor on the error side is an ordinary outer frame; the unframed indexed side is shared across both actual frame rows. -/
example :
    (framedEvaluated? framedData).map
      (·.map fun result => (result.key, result.outcome)) =
    some [
      (.text "Engineering", .notFired),
      (.text "Legal", .notFired),
      (.text "Operations", .notFired),
      (.text "Sales", framedFired [1, 1]),
      (.text "Legal", .notFired),
      (.text "Operations", framedFired [2, 2]),
      (.text "Sales", framedFired [2, 1])
    ] := by
  native_decide

/- The public row result retains the complete frame environment, so equal keys from different outer rows remain distinguishable without reconstructing topology. -/
example :
    (framedEvaluated? framedData).map
      (·.map fun result =>
        (result.outerEnvironment, result.key)) =
    some [
      ([(50, 1)], .text "Engineering"),
      ([(50, 1)], .text "Legal"),
      ([(50, 1)], .text "Operations"),
      ([(50, 1)], .text "Sales"),
      ([(50, 2)], .text "Legal"),
      ([(50, 2)], .text "Operations"),
      ([(50, 2)], .text "Sales")
    ] := by
  native_decide

/- Operand order does not choose the frame: the checked scope relation binds the right column when the emitted error operand is authored second. -/
example :
    (rightFramedEvaluated? framedData).map
      (·.map fun result => (result.key, result.outcome)) =
    (framedEvaluated? framedData).map
      (·.map fun result => (result.key, result.outcome)) := by
  native_decide

/- A framed parallel rule cannot emit on the shared side because that declaration has no coordinate for the ordinary outer frame. -/
example :
    (match checkParallelPresenceRule
        framedModel 22 24 24 "FPI" .error messagePlan with
      | .error error => some error
      | .ok _ => none) =
      some (.errorFieldNotOnFramedSide 24) := by
  native_decide

private def indexedFrameModel : FlatModel := {
  fields := [
    {
      id := 25
      groupPath := frame.path
      name := "FrameKey"
      policy := { kind := .string }
      repeatableScope := [50]
    }
  ] ++ framedModel.fields
  repeatableGroups := [
    { frame with indexField := some 25 },
    framedDemand,
    framedSupply
  ]
}

/- A frame with its own index is a second indexed ancestor on the error path, not the one legal non-indexed outer-loop shape. -/
example :
    (match checkParallelPresenceRule
        indexedFrameModel 22 24 22 "IFPI" .error messagePlan with
      | .error error => some error
      | .ok _ => none) =
      some (.multipleIndexedOperandGroups 22
        [frame.path, framedDemand.path]) := by
  native_decide

/- Column invalidity is scoped to the current frame: a clean unmatched shared key stays false in frame one and becomes UNKNOWN only in invalid frame two. -/
example :
    (framedEvaluated? invalidSecondFrameData).map
      (·.map fun result => (result.key, result.outcome)) =
    some [
      (.text "Engineering", .notFired),
      (.text "Legal", .notFired),
      (.text "Operations", .notFired),
      (.text "Sales", framedFired [1, 1]),
      (.text "Legal", .unknown),
      (.text "Operations", framedFired [2, 2]),
      (.text "Sales", framedFired [2, 1])
    ] := by
  native_decide

/- An instantiated frame row above its model limit never creates another keyed evaluation. -/
example :
    (framedEvaluated? overLimitFrameData).map
      (·.map fun result => (result.key, result.outcome)) =
    (framedEvaluated? framedData).map
      (·.map fun result => (result.key, result.outcome)) := by
  native_decide

private def otherFrame : RepeatableGroupDecl := {
  level := 80
  path := ["Plan", "OtherFrame"]
  repeatability := some 2
}

private def otherFramedDemand : RepeatableGroupDecl := {
  level := 60
  path := framedDemand.path
  repeatability := some 3
  indexField := some 31
}

private def otherFramedSupply : RepeatableGroupDecl := {
  level := 90
  path := ["Plan", "OtherFrame", "Supply"]
  repeatability := some 2
  indexField := some 33
}

private def twoFramedSidesModel : FlatModel := {
  fields := [
    {
      (wrappedIndexDecl 31 otherFramedDemand.path 60) with
        repeatableScope := [50, 60]
    },
    {
      (wrappedTargetDecl 32 otherFramedDemand.path 60) with
        repeatableScope := [50, 60]
    },
    {
      (wrappedIndexDecl 33 otherFramedSupply.path 90) with
        repeatableScope := [80, 90]
    },
    {
      (wrappedTargetDecl 34 otherFramedSupply.path 90) with
        repeatableScope := [80, 90]
    }
  ]
  repeatableGroups := [
    frame, otherFramedDemand, otherFrame, otherFramedSupply
  ]
}

/- Distinct repeatable frames on both joined sides are not one nested outer loop and remain structurally incompatible. -/
example :
    (match checkParallelPresenceRule
        twoFramedSidesModel 32 34 32 "TFPI" .error messagePlan with
      | .error error => some error
      | .ok _ => none) =
      some (.join
        (.incompatibleGroups
          otherFramedDemand.path otherFramedSupply.path)) := by
  native_decide

private def disjointLeft : RepeatableGroupDecl := {
  level := 80
  path := ["Left"]
  repeatability := some 2
  indexField := some 31
}

private def disjointRight : RepeatableGroupDecl := {
  level := 90
  path := ["Right"]
  repeatability := some 2
  indexField := some 32
}

private def disjointModel : FlatModel := {
  fields := [
    wrappedIndexDecl 31 disjointLeft.path 80,
    wrappedIndexDecl 32 disjointRight.path 90
  ]
  repeatableGroups := [disjointLeft, disjointRight]
}

/- Equal empty outer repeatable scopes do not manufacture a cross-root join; the groups still need a real common group ancestor. -/
example :
    (match checkParallelIndexGroups disjointModel
        disjointLeft disjointRight with
      | .error error => some error
      | .ok _ => none) =
      some (.incompatibleGroups disjointLeft.path disjointRight.path) := by
  native_decide

end A12Kernel.Conformance.ParallelPresenceRule
