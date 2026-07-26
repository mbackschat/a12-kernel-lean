import A12Kernel.Elaboration.ParallelNumericRun
import A12Kernel.Conformance.ParallelNumericAlternativeTable

/-! # Parallel Number run-plan and overlay locks -/

namespace A12Kernel.Conformance.ParallelNumericRun

open A12Kernel
open A12Kernel.Conformance.ParallelNumericThreeGroupOperands

private def literal (value : Rat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

private def rowExpression? (target : FieldId)
    (operand : SurfaceFieldPath)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (guard : ComputationCondition)
    (suppressExactScaleWarning : Bool := false) :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    model ["Plan"] target operand expression (some guard)
      suppressExactScaleWarning).toOption

private def row? (target : FieldId) (operand : SurfaceFieldPath)
    (guard : ComputationCondition) :=
  rowExpression? target operand (.atom (.field operand)) guard

private def table? (target : FieldId) (operand : SurfaceFieldPath)
    (guardField : FieldId) :
    Option (CheckedParallelNumericAlternativeTable model) := do
  let first ← row? target operand (.fieldFilled guardField)
  let second ← row? target operand (.fieldNotFilled guardField)
  (certifyParallelNumericAlternativeTable [first, second]).toOption

private def checkedRun?
    (producer consumer :
      Option (CheckedParallelNumericAlternativeTable model)) :
    Option (CheckedParallelNumericRun model) := do
  let producer ← producer
  let consumer ← consumer
  (certifyParallelNumericRun producer consumer).toOption

private def run? : Option (CheckedParallelNumericRun model) :=
  checkedRun? (table? 4 offsetPath 6) (table? 2 inputPath 4)

private def invalidProducerTable? :
    Option (CheckedParallelNumericAlternativeTable model) := do
  let divide :=
    AuthoredNumericExpr.binary .divide
      (.atom (.field offsetPath)) (literal 0)
  let first ← rowExpression? 4 offsetPath divide (.fieldFilled 6) true
  let second ← rowExpression? 4 offsetPath divide (.fieldNotFilled 6) true
  (certifyParallelNumericAlternativeTable [first, second]).toOption

private def noValueProducerTable? :
    Option (CheckedParallelNumericAlternativeTable model) := do
  let first ← row? 4 offsetPath (.fieldFilled 7)
  let second ← row? 4 offsetPath (.fieldFilled 7)
  (certifyParallelNumericAlternativeTable [first, second]).toOption

private def unreadProducerConsumerTable? :
    Option (CheckedParallelNumericAlternativeTable model) := do
  let guard := ComputationCondition.or
    (.fieldFilled 6) (.fieldNotFilled 6)
  let first ← row? 2 offsetPath guard
  let second ← row? 2 inputPath (.fieldFilled 4)
  (certifyParallelNumericAlternativeTable [first, second]).toOption

private def checkedDocument? (cells : List ClassifiedCellInput) :=
  (preliminaryFor cells).map (·.base)

private def read? (state : ParallelNumericRunState)
    (cells : List ClassifiedCellInput) (address : CellAddr) :
    Option CheckedCell := do
  let run ← run?
  let document ← checkedDocument? cells
  (run.readPolicy state document address).toOption

private def accepted (field : FieldId) (path : List Nat)
    (value : Int) : ParallelNumericDirectOutcome := {
  address := { field, path }
  outcome := .accepted { unscaled := value, scale := 0 }
}

private def outcomes?
    (checked : Option (CheckedParallelNumericRun model))
    (cells : List ClassifiedCellInput) :
    Option (List ParallelNumericDirectOutcome) := do
  let run ← checked
  let preliminary ← preliminaryFor cells
  (run.execute preliminary).toOption

private def result?
    (checked : Option (CheckedParallelNumericRun model))
    (cells : List ClassifiedCellInput) :
    Option (NumericComputationRunView Bool CellAddr) := do
  let run ← checked
  let preliminary ← preliminaryFor cells
  (run.executeResult preliminary []).toOption

private def computedNumberCell (field : FieldId) (path : List Nat)
    (stored : StoredNumber) : ClassifiedCellInput := {
  address := { field, path }
  stored := stored.render
  raw := .parsed (.num stored.amount)
  numericSourceIdentity := some (.decimal stored)
}

/- The checked direction is producer first; duplicate or reversed roles fail structurally. -/
example :
    (do
      let producer ← table? 4 offsetPath 6
      match certifyParallelNumericRun producer producer with
      | .error error => some error
      | .ok _ => none) = some (.duplicateTarget 4) ∧
    (do
      let producer ← table? 4 offsetPath 6
      let consumer ← table? 2 inputPath 4
      match certifyParallelNumericRun consumer producer with
      | .error error => some error
      | .ok _ => none) =
        some (.producerReadsConsumer 2 4) ∧
    (do
      let producer ← table? 4 offsetPath 6
      let independent ← table? 2 offsetPath 6
      match certifyParallelNumericRun producer independent with
      | .error error => some error
      | .ok _ => none) =
        some (.consumerDoesNotReadProducer 2 4) := by
  native_decide

/- Pending computed addresses hide stale input, and completion is exact to one repetition address. -/
example :
    let stale := (cleanCells.filter fun cell => cell.address.field != 4) ++ [
      numberCell 4 [1] { unscaled := 99, scale := 0 },
      numberCell 4 [2] { unscaled := 98, scale := 0 }
    ]
    (read? {} stale { field := 4, path := [1] }).map
        (observeCell .computation) = some CellObservation.empty ∧
      (read? { completed := [accepted 4 [1] 30] }
        stale { field := 4, path := [1] }).map
          (observeCell .computation) =
        some (CellObservation.value (.num 30)) ∧
      (read? { completed := [accepted 4 [1] 30] }
        stale { field := 4, path := [2] }).map
          (observeCell .computation) =
        some CellObservation.empty := by
  native_decide

/- Invalid producer classes collapse to cause-blind dependency poison, while an ordinary input delegates unchanged. -/
example :
    let invalid : ParallelNumericDirectOutcome := {
      address := { field := 4, path := [1] }
      outcome := .invalidNoValue .calculationValue
    }
    (read? { completed := [invalid] }
      cleanCells { field := 4, path := [1] }).map
        (observeCell .computation) =
        some (CellObservation.poison .computedDependency) ∧
      (read? {} cleanCells { field := 6, path := [1] }).map
        (observeCell .computation) =
        some (CellObservation.value (.num 1)) := by
  native_decide

/- Producer outcomes replace stale addressed inputs before the dependent table runs. -/
example :
    (outcomes? run? cleanCells).map (·.map (fun result =>
      (result.address, result.outcome))) =
      some [
        ({ field := 4, path := [1] },
          .accepted { unscaled := 1, scale := 0 }),
        ({ field := 4, path := [2] },
          .accepted { unscaled := 0, scale := 0 }),
        ({ field := 2, path := [1] },
          .accepted { unscaled := 1, scale := 0 }),
        ({ field := 2, path := [2] },
          .accepted { unscaled := 0, scale := 0 })
      ] := by
  native_decide

/- Clean producer no-value reads as numeric empty/zero; reached producer invalidity poisons the dependent target. -/
example :
    (outcomes?
      (checkedRun? noValueProducerTable? (table? 2 inputPath 4))
      cleanCells).map (·.map (·.outcome)) =
        some [
          .noValue, .noValue,
          .accepted { unscaled := 0, scale := 0 },
          .accepted { unscaled := 0, scale := 0 }
        ] ∧
      (outcomes?
        (checkedRun? invalidProducerTable? (table? 2 inputPath 4))
        cleanCells).map (·.map (·.outcome)) =
        some [
          .invalidNoValue .calculationValue,
          .invalidNoValue .calculationValue,
          .inheritedPoison .computedDependency,
          .inheritedPoison .computedDependency
        ] := by
  native_decide

/- Static dependency orders the tables but does not poison a selected row that never reads the invalid producer. -/
example :
    (outcomes?
      (checkedRun? invalidProducerTable? unreadProducerConsumerTable?)
      cleanCells).map (·.map (·.outcome)) =
      some [
        .invalidNoValue .calculationValue,
        .invalidNoValue .calculationValue,
        .accepted { unscaled := 1, scale := 0 },
        .accepted { unscaled := 0, scale := 0 }
      ] := by
  native_decide

/- Combined classification retains producer and consumer instances in the shared addressed Number result domain. -/
example :
    let source :=
      (cleanCells.filter fun cell => cell.address.field != 4) ++ [
        computedNumberCell 4 [1] { unscaled := 10, scale := 0 },
        computedNumberCell 4 [2] { unscaled := 20, scale := 0 }
    ]
    ((result? run? source).map fun view =>
      (view.withoutErrors.map fun computed =>
        (computed.targetField, computed.value), view.cleared)) =
      some ([
        ({ field := 4, path := [1] },
          { unscaled := 1, scale := 0 }),
        ({ field := 4, path := [2] },
          { unscaled := 0, scale := 0 }),
        ({ field := 2, path := [1] },
          { unscaled := 1, scale := 0 }),
        ({ field := 2, path := [2] },
          { unscaled := 0, scale := 0 })
      ], []) := by
  native_decide

end A12Kernel.Conformance.ParallelNumericRun
