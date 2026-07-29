import A12Kernel.Elaboration.ParallelComputationClearingApplication
import A12Kernel.Elaboration.NumericComputation.RunApplication
import A12Kernel.Elaboration.ParallelNumericDirectRun
import A12Kernel.Elaboration.ParallelNumericDirectRunResult

/-! # Checked parallel-computation clearing-plan locks -/

namespace A12Kernel.Conformance.ParallelComputationClearingPlan

open A12Kernel

private def indexDeclaration (id : FieldId) (path : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := path
  name := "Key"
  policy := { kind := .string }
  repeatableScope := scope
}

private def numberDeclaration (id : FieldId) (path : GroupPath)
    (name : String) (scope : List RepeatableLevel) (scale : Nat := 0) :
    FlatFieldDecl := {
  id
  groupPath := path
  name
  policy := { kind := .number { scale, signed := false } }
  repeatableScope := scope
}

private def frame : RepeatableGroupDecl := {
  level := 50
  path := ["Plan", "Frame"]
  repeatability := some 2
}

private def targetGroup : RepeatableGroupDecl := {
  level := 60
  path := ["Plan", "Frame", "Target"]
  repeatability := some 2
  indexField := some 1
}

private def operandGroup : RepeatableGroupDecl := {
  level := 70
  path := ["Plan", "Operand"]
  repeatability := some 2
  indexField := some 3
}

/-- Shared checked-route fixture used by the focused parallel Number conformance modules. -/
def model : FlatModel := {
  fields := [
    indexDeclaration 1 targetGroup.path [50, 60],
    numberDeclaration 2 targetGroup.path "Result" [50, 60],
    numberDeclaration 5 targetGroup.path "Peer" [50, 60],
    indexDeclaration 3 operandGroup.path [70],
    numberDeclaration 4 operandGroup.path "Input" [70],
    numberDeclaration 6 operandGroup.path "Offset" [70]
  ]
  repeatableGroups := [frame, targetGroup, operandGroup]
}

private def scaleMismatchModel : FlatModel := {
  model with
  fields := model.fields.map fun declaration =>
    if declaration.id == 4 then
      numberDeclaration 4 operandGroup.path "Input" [70] 1
    else declaration
}

/-- Exact ordinary operand path selected by the shared parallel route fixture. -/
def operandPath : SurfaceFieldPath := {
  base := .absolute
  groups := operandGroup.path
  field := "Input"
}

private def checked? :=
  (checkParallelNumericComputationClearingPlan
    model ["Plan"] 2 operandPath).toOption

private def directChecked? :=
  (checkIsolatedParallelNumericDirectRun
    model ["Plan"] 2 operandPath).toOption

private def guardedDirectChecked? :=
  (checkIsolatedParallelNumericDirectRunWithGuard
    model ["Plan"] 2 operandPath
      (some (.fieldFilled 4))).toOption

private def incrementExpression :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add
    (.atom (.field operandPath))
    (.literal { value := 1, authoredScale := 0 })

private def expressionChecked? :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    model ["Plan"] 2 operandPath incrementExpression none).toOption

private def wrappedExpression :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .round .halfUp omittedRoundingPlaces
    (.abs (AuthoredNumericExpr.extremumList .minimum
      (.binary .subtract
        (.atom (.field operandPath))
        (.literal { value := 150, authoredScale := 0 }))
      [.literal { value := -25, authoredScale := 0 }]))

private def wrappedExpressionChecked? :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    model ["Plan"] 2 operandPath wrappedExpression none).toOption

private def world : World := { now := { epochMillis := 0 } }

private def rows : List RowAddr := [
  { group := 50, path := [1] },
  { group := 60, path := [1, 1] },
  { group := 70, path := [1] },
  { group := 50, path := [2] },
  { group := 60, path := [2, 1] },
  { group := 60, path := [1, 2] },
  { group := 70, path := [2] }
]

private def indexCell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.str stored)
}

private def numericCell (path : List Nat) (stored : StoredNumber) :
    ClassifiedCellInput := {
  address := { field := 2, path }
  stored := stored.render
  raw := .parsed (.num stored.amount)
  numericDecimal := some {
    unscaled := stored.unscaled
    scale := stored.scale
  }
}

/-- One typed operand placement at an exact repeatable path. -/
def operandNumericCell (path : List Nat) (stored : StoredNumber) :
    ClassifiedCellInput := {
  address := { field := 4, path }
  stored := stored.render
  raw := .parsed (.num stored.amount)
}

private def emptyNumericCell (path : List Nat) :
    ClassifiedCellInput := {
  address := { field := 2, path }
  stored := ""
  raw := .presentEmpty
}

private def stringValuedNumericCell (path : List Nat)
    (stored : StoredNumber) : ClassifiedCellInput := {
  address := { field := 2, path }
  stored := stored.render
  raw := .parsed (.num stored.amount)
}

/-- Complete clean exact-text index columns for the shared target rows. -/
def cleanIndexCells : List ClassifiedCellInput := [
  indexCell 1 [1, 1] "Alpha",
  indexCell 1 [1, 2] "Beta",
  indexCell 1 [2, 1] "Gamma",
  indexCell 3 [1] "Alpha",
  indexCell 3 [2] "Beta"
]

private def sourceWith (cells : List ClassifiedCellInput) :
    DocumentData := { instantiatedRows := rows, cells }

private def checkedDocument? : Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" (sourceWith [])).toOption

/-- Build the one checked preliminary consumed by every route crossing in these fixtures. -/
def preliminaryFor (cells : List ClassifiedCellInput) :
    Option (CheckedIndexPreliminary model) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler model).toOption
  let checked ←
    (checkDocument prepared "en_US" (sourceWith cells)).toOption
  checked.applyFullIndexPreliminary.toOption

private def markCoordinates?
    (cells : List ClassifiedCellInput)
    (side : ParallelComputationIndexSide) :
    Option (List (List Nat)) := do
  let checked ← checked?
  let preliminary ← preliminaryFor cells
  let marks ← (checked.invalidIndexMarks preliminary side).toOption
  pure (marks.map (·.coordinates))

private def clearingResult?
    (cells : List ClassifiedCellInput) :
    Option (Except ParallelNumericClearingError
      ParallelNumericClearingView) := do
  let checked ← checked?
  let preliminary ← preliminaryFor cells
  pure (checked.clearedSourceTargets preliminary)

private def clearedAddresses?
    (cells : List ClassifiedCellInput) : Option (List CellAddr) :=
  (clearingResult? cells).bind fun result =>
    result.toOption.map (·.cleared)

private def applicationDestination : AddressedNumericDestination :=
  fun address =>
    if address == { field := 2, path := [1, 1] } then
      .presentValue (.decimal { unscaled := 70, scale := 1 })
    else if address == { field := 2, path := [2, 1] } then
      .absent
    else
      .presentValue (.decimal { unscaled := 9, scale := 0 })

private def appliedDestination?
    (cells : List ClassifiedCellInput) :
    Option AddressedNumericDestination := do
  let checked ← checked?
  let preliminary ← preliminaryFor cells
  let view ← (checked.clearedSourceTargets preliminary).toOption
  pure (view.applyTo applicationDestination)

private def directOutcomes?
    (cells : List ClassifiedCellInput) :
    Option (List ParallelNumericDirectOutcome) := do
  let checked ← directChecked?
  let preliminary ← preliminaryFor cells
  (checked.execute preliminary).toOption

private def directView?
    (cells : List ClassifiedCellInput) :
    Option
      (NumericComputationRunView (ComputationFormalMessage Bool) CellAddr) := do
  let checked ← directChecked?
  let preliminary ← preliminaryFor cells
  (checked.executeResult preliminary (fun _ => true) []).toOption

private def guardedDirectOutcomes?
    (cells : List ClassifiedCellInput) :
    Option (List ParallelNumericDirectOutcome) := do
  let checked ← guardedDirectChecked?
  let preliminary ← preliminaryFor cells
  (checked.execute preliminary).toOption

private def expressionOutcomes?
    (cells : List ClassifiedCellInput) :
    Option (List ParallelNumericDirectOutcome) := do
  let checked ← expressionChecked?
  let preliminary ← preliminaryFor cells
  (checked.execute preliminary).toOption

private def wrappedExpressionOutcomes?
    (cells : List ClassifiedCellInput) :
    Option (List ParallelNumericDirectOutcome) := do
  let checked ← wrappedExpressionChecked?
  let preliminary ← preliminaryFor cells
  (checked.execute preliminary).toOption

private def guardedDirectView?
    (cells : List ClassifiedCellInput) :
    Option
      (NumericComputationRunView (ComputationFormalMessage Bool) CellAddr) := do
  let checked ← guardedDirectChecked?
  let preliminary ← preliminaryFor cells
  (checked.executeResult preliminary (fun _ => true) []).toOption

private def appliedDirectView?
    (cells : List ClassifiedCellInput)
    (address : CellAddr) : Option NumericTargetState := do
  let view ← directView? cells
  let applied ← view.applyTo applicationDestination |>.toOption
  pure (applied address)

/- Target instances come from physical rows at the deepest target scope, including blank-but-instantiated rows; unrelated group rows do not enter the projection. Document order is the Lean account's deterministic internal order, not a Kernel clearing-order claim. -/
example :
    (checked?.bind fun checked =>
      checkedDocument?.bind fun document =>
        (checked.targetEnvironments document).toOption) =
      some [
        [(50, 1), (60, 1)],
        [(50, 2), (60, 1)],
        [(50, 1), (60, 2)]
      ] := by
  native_decide

/- A clean checked index column emits no mark on either side. -/
example :
    markCoordinates? cleanIndexCells .target = some [] ∧
      markCoordinates? cleanIndexCells .operand = some [] := by
  native_decide

/- An unavailable target-path index marks only its frame, while the same clean document leaves the off-path operand side unmarked. -/
example :
    let targetInvalid := cleanIndexCells.filter fun input =>
      input.address != { field := 1, path := [2, 1] }
    markCoordinates? targetInvalid .target = some [[2]] ∧
      markCoordinates? targetInvalid .operand = some [] := by
  native_decide

/- An unavailable off-path operand index collapses to one root mark covering every target frame; the clean target-path column contributes nothing. -/
example :
    let operandInvalid := cleanIndexCells.filter fun input =>
      input.address != { field := 3, path := [2] }
    markCoordinates? operandInvalid .target = some [] ∧
      markCoordinates? operandInvalid .operand = some [[]] := by
  native_decide

/- Public clearing remains source-relative: an invalid target-path frame clears its filled target only, not a clean sibling frame. -/
example :
    let targetInvalid :=
      (cleanIndexCells.filter fun input =>
        input.address != { field := 1, path := [2, 1] }) ++ [
          numericCell [1, 1] { unscaled := 7, scale := 0 },
          numericCell [2, 1] { unscaled := 8, scale := 0 }
        ]
    clearedAddresses? targetInvalid =
      some [{ field := 2, path := [2, 1] }] := by
  native_decide

/- An off-path invalid column suppresses every covered target outcome; source-filled targets appear only in the clearing projection. -/
example :
    let operandInvalid :=
      (cleanIndexCells.filter fun input =>
        input.address != { field := 3, path := [2] }) ++ [
          operandNumericCell [1] { unscaled := 100, scale := 0 },
          numericCell [1, 1] { unscaled := 7, scale := 0 },
          numericCell [2, 1] { unscaled := 8, scale := 0 }
        ]
    directOutcomes? operandInvalid = some [] ∧
      clearedAddresses? operandInvalid =
        some [
          { field := 2, path := [1, 1] },
          { field := 2, path := [2, 1] }
        ] := by
  native_decide

/- Decimal-valued and String-valued target inputs are both complete checked regimes; index coverage decides clearing independently of that source identity. -/
example :
    let targetInvalid :=
      cleanIndexCells.filter fun input =>
        input.address != { field := 1, path := [2, 1] }
    let unmarkedString := targetInvalid ++ [
      stringValuedNumericCell [1, 1] { unscaled := 7, scale := 0 },
      numericCell [2, 1] { unscaled := 8, scale := 0 }
    ]
    let markedString := targetInvalid ++ [
      numericCell [1, 1] { unscaled := 7, scale := 0 },
      stringValuedNumericCell [2, 1] { unscaled := 8, scale := 0 }
    ]
    ((clearedAddresses? unmarkedString ==
        some [{ field := 2, path := [2, 1] }]) &&
      clearedAddresses? markedString ==
        some [{ field := 2, path := [2, 1] }]) = true := by
  native_decide

/- A root off-path mark covers every target row, but public clearing retains only source-filled targets and excludes an explicitly empty sibling. -/
example :
    let operandInvalid :=
      (cleanIndexCells.filter fun input =>
        input.address != { field := 3, path := [2] }) ++ [
          numericCell [1, 1] { unscaled := 7, scale := 0 },
          emptyNumericCell [1, 2],
          numericCell [2, 1] { unscaled := 8, scale := 0 }
        ]
    clearedAddresses? operandInvalid =
      some [
        { field := 2, path := [1, 1] },
        { field := 2, path := [2, 1] }
      ] := by
  native_decide

/- Clean target rows copy the matching operand by index key; an unmatched clean operand side contributes numeric zero rather than suppressing that target. -/
example :
    let clean := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 }
    ]
    directOutcomes? clean =
      some [
        ⟨{ field := 2, path := [1, 1] },
          .accepted { unscaled := 100, scale := 0 }⟩,
        ⟨{ field := 2, path := [2, 1] },
          .accepted { unscaled := 0, scale := 0 }⟩,
        ⟨{ field := 2, path := [1, 2] },
          .accepted { unscaled := 200, scale := 0 }⟩
      ] := by
  native_decide

/- Operand-list extrema, absolute value, and rounding compose over the same joined read through the shared operation tree. -/
example :
    let clean := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 }
    ]
    (wrappedExpressionOutcomes? clean).map
        (List.map fun result => result.outcome) =
      some [
        .accepted { unscaled := 50, scale := 0 },
        .accepted { unscaled := 150, scale := 0 },
        .accepted { unscaled := 25, scale := 0 }
      ] := by
  native_decide

/- The parallel route supplies the sole field atom while the shared numeric tree retains ordinary arithmetic and literal scale. An unmatched joined operand is still numeric zero before the addition. -/
example :
    let clean := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 }
    ]
    expressionOutcomes? clean =
      some [
        ⟨{ field := 2, path := [1, 1] },
          .accepted { unscaled := 101, scale := 0 }⟩,
        ⟨{ field := 2, path := [2, 1] },
          .accepted { unscaled := 1, scale := 0 }⟩,
        ⟨{ field := 2, path := [1, 2] },
          .accepted { unscaled := 201, scale := 0 }⟩
      ] := by
  native_decide

/- A computed target-group field is not an operand route; admitting it would bypass the checked target self-reference boundary. -/
example :
    let peerPath : SurfaceFieldPath := {
      base := .absolute
      groups := targetGroup.path
      field := "Peer"
    }
    (match checkIsolatedParallelNumericExpressionRunWithGuard
        model ["Plan"] 2 operandPath (.atom (.field peerPath)) none with
    | .error error => some error
    | .ok _ => none) =
      some .expressionNotLimitedToOperand := by
  native_decide

/- A literal-only expression cannot retain an irrelevant parallel route. -/
example :
    (match checkIsolatedParallelNumericExpressionRunWithGuard
        model ["Plan"] 2 operandPath
          (.literal { value := 1, authoredScale := 0 }) none with
    | .error error => some error
    | .ok _ => none) =
      some .expressionNotLimitedToOperand := by
  native_decide

/- A clean false guard is an outcome-derived no-value, not an index failure: a stale source at that exact target enters the ordinary result clear collection. -/
example :
    let source := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 },
      numericCell [2, 1] { unscaled := 8, scale := 0 }
    ]
    (guardedDirectView? source).map (·.cleared) =
      some [{ field := 2, path := [2, 1] }] := by
  native_decide

/- A guard over the joined operand runs before the direct copy: matching filled rows compute, while a clean unmatched operand selects no operation and retains an exact no-value outcome. -/
example :
    let clean := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 }
    ]
    guardedDirectOutcomes? clean =
      some [
        ⟨{ field := 2, path := [1, 1] },
          .accepted { unscaled := 100, scale := 0 }⟩,
        ⟨{ field := 2, path := [2, 1] }, .noValue⟩,
        ⟨{ field := 2, path := [1, 2] },
          .accepted { unscaled := 200, scale := 0 }⟩
      ] := by
  native_decide

/- One checked input owns execution, addressed source comparison, and public classification: exact source identity removes only the unchanged success from the changed subset. -/
example :
    let clean := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 },
      numericCell [1, 1] { unscaled := 100, scale := 0 },
      numericCell [1, 2] { unscaled := 7, scale := 0 }
    ]
    ((directView? clean).map fun view =>
      (view.withoutErrors, view.withChanges, view.withErrors, view.cleared)) =
      some (
        [
          ⟨{ field := 2, path := [1, 1] },
            { unscaled := 100, scale := 0 }⟩,
          ⟨{ field := 2, path := [2, 1] },
            { unscaled := 0, scale := 0 }⟩,
          ⟨{ field := 2, path := [1, 2] },
            { unscaled := 200, scale := 0 }⟩
        ],
        [
          ⟨{ field := 2, path := [2, 1] },
            { unscaled := 0, scale := 0 }⟩,
          ⟨{ field := 2, path := [1, 2] },
            { unscaled := 200, scale := 0 }⟩
        ],
        [],
        []) := by
  native_decide

/- Addressed full-result application preserves an unchanged success even when the destination differs, applies changed successes at their exact addresses, and leaves unrelated addresses untouched. -/
example :
    let clean := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 },
      numericCell [1, 1] { unscaled := 100, scale := 0 },
      numericCell [1, 2] { unscaled := 7, scale := 0 }
    ]
    appliedDirectView? clean { field := 2, path := [1, 1] } =
        some (.presentValue (.decimal { unscaled := 70, scale := 1 })) ∧
      appliedDirectView? clean { field := 2, path := [2, 1] } =
        some (.presentValue (.decimal { unscaled := 0, scale := 0 })) ∧
      appliedDirectView? clean { field := 2, path := [1, 2] } =
        some (.presentValue (.decimal { unscaled := 200, scale := 0 })) ∧
      appliedDirectView? clean { field := 5, path := [1, 1] } =
        some (.presentValue (.decimal { unscaled := 9, scale := 0 })) := by
  native_decide

/- An on-path invalid frame contributes no outcome for its marked target, while clean sibling-frame targets still execute and the source-filled invalid target remains solely in the clearing projection. -/
example :
    let targetInvalid :=
      (cleanIndexCells.filter fun input =>
        input.address != { field := 1, path := [2, 1] }) ++ [
          operandNumericCell [1] { unscaled := 100, scale := 0 },
          operandNumericCell [2] { unscaled := 200, scale := 0 },
          numericCell [2, 1] { unscaled := 8, scale := 0 }
        ]
    (directOutcomes? targetInvalid).map (List.map (·.address)) =
        some [
          { field := 2, path := [1, 1] },
          { field := 2, path := [1, 2] }
        ] ∧
      clearedAddresses? targetInvalid =
        some [{ field := 2, path := [2, 1] }] := by
  native_decide

/- Post-loop index invalidity and successful outcomes are classified together from the same preliminary: the blocked filled target is cleared and never appears as a success. -/
example :
    let targetInvalid :=
      (cleanIndexCells.filter fun input =>
        input.address != { field := 1, path := [2, 1] }) ++ [
          operandNumericCell [1] { unscaled := 100, scale := 0 },
          operandNumericCell [2] { unscaled := 200, scale := 0 },
          numericCell [2, 1] { unscaled := 8, scale := 0 }
        ]
    ((directView? targetInvalid).map fun view =>
      (view.withoutErrors.map (·.targetField), view.cleared)) =
      some (
        [
          { field := 2, path := [1, 1] },
          { field := 2, path := [1, 2] }
        ],
        [{ field := 2, path := [2, 1] }]) := by
  native_decide

/- The low-level additive-clear constructor deliberately carries no provenance guarantee; the checked parallel result boundary detects a fabricated outcome/index-clear collision instead of inheriting that false law. -/
example :
    let address : CellAddr := { field := 2, path := [1, 1] }
    let classified :=
      NumericComputationRunView.fromPartitionedSourceOutcomes
        ([] : List Bool) [
        {
          targetField := address
          outcome := .accepted { unscaled := 1, scale := 0 }
          source := .absent
        }
      ]
    let malformed := classified.withAdditionalClears [address]
    parallelNumericDirectClassifiedIndexClear?
        malformed [address] = some address ∧
      (match malformed.applyTo applicationDestination with
      | .error (.duplicateActionTarget duplicate) => duplicate == address
      | .ok _ => false) = true := by
  native_decide

/- Addressed clearing empties a present destination target in place, leaves an absent covered target absent, and preserves an unrelated address. -/
example :
    let operandInvalid :=
      (cleanIndexCells.filter fun input =>
        input.address != { field := 3, path := [2] }) ++ [
          numericCell [1, 1] { unscaled := 7, scale := 0 },
          numericCell [2, 1] { unscaled := 8, scale := 0 }
        ]
    ((appliedDestination? operandInvalid).map fun destination =>
      (destination { field := 2, path := [1, 1] },
        destination { field := 2, path := [2, 1] },
        destination { field := 5, path := [1, 1] })) =
      some (.presentEmpty, .absent,
        .presentValue (.decimal { unscaled := 9, scale := 0 })) := by
  native_decide

/- Each checked index side derives its asymmetric common-prefix mark scope without a caller-supplied truncation width. -/
example :
    (checked?.map fun checked =>
      ((checked.markPlanFor .target).sharedScope,
        (checked.markPlanFor .operand).sharedScope)) =
      some ([50], []) := by
  native_decide

/- The checked scopes reproduce the observed discriminator: an on-path malformed key keeps frame siblings distinct, while an off-path malformed key covers both. -/
example :
    (checked?.bind fun checked => do
      let onPath ←
        (checked.markPlanFor .target).markForUnavailable
          (some .duplicateIndex) [(50, 1), (60, 1)] |>.toOption
      let offPath ←
        (checked.markPlanFor .operand).markForUnavailable
          (some .duplicateIndex) [(50, 1), (60, 1)] |>.toOption
      let onFirst ←
        (checked.markPlanFor .target).covers
          (← onPath) [(50, 1), (60, 1)] |>.toOption
      let onSecond ←
        (checked.markPlanFor .target).covers
          (← onPath) [(50, 2), (60, 1)] |>.toOption
      let offSecond ←
        (checked.markPlanFor .operand).covers
          (← offPath) [(50, 2), (60, 1)] |>.toOption
      pure (onFirst, onSecond, offSecond)) =
      some (true, false, true) := by
  native_decide

/- The ordinary non-starred operand and repeatable target determine both indexed groups and scopes without caller-supplied groups or a route bit. -/
example :
    (checked?.map fun checked =>
      (checked.groups.leftGroup.path,
        checked.groups.rightGroup.path,
        checked.targetDeclaration.repeatableScope,
        checked.operandDeclaration.repeatableScope)) =
      some (targetGroup.path, operandGroup.path, [50, 60], [70]) := by
  native_decide

/- A second ordinary field in the target's own indexed group is not a parallel route. -/
example :
    (match checkParallelNumericComputationClearingPlan model ["Plan"] 2 {
        base := .absolute
        groups := targetGroup.path
        field := "Peer"
      } with
    | .error error => some error
    | .ok _ => none) =
      some (.join (.incompatibleGroups targetGroup.path targetGroup.path)) := by
  native_decide

/- A direct field copy retains computation's shared exact-scale gate rather than treating any two Number declarations as assignable. -/
example :
    (match checkIsolatedParallelNumericDirectRun
        scaleMismatchModel ["Plan"] 2 operandPath with
    | .error error => some error
    | .ok _ => none) =
      some (.operationScaleMismatch 0 (NumericScaleSummary.field 1)) := by
  native_decide

end A12Kernel.Conformance.ParallelComputationClearingPlan
