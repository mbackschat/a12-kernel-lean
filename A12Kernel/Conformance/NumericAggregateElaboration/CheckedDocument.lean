import A12Kernel.Conformance.NumericAggregateElaboration.Support

/-! # Checked-document numeric entity aggregate locks and shared checked fixtures -/

namespace A12Kernel.Conformance.NumericAggregateElaboration.CheckedDocument

open A12Kernel
open A12Kernel.Conformance.NumericAggregateElaboration.Support

def aggregateHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner, field := absolute ["Form", "Rows"] "Amount" }
    { origin := .inner, field := absolute ["Form", "Rows"] "Amount" }

def computationAggregateHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner, field := absolute ["Form", "Rows"] "FilterLeft" }
    { origin := .inner, field := absolute ["Form", "Rows"] "FilterRight" }

def aggregateSource (first : SurfaceNumberEntityOperand)
    (rest : List SurfaceNumberEntityOperand) : SurfaceNumberEntitySource :=
  { first, rest }

def aggregateDocument (rows : List RowIndex) : Document :=
  { instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none }

def aggregateStarRead (a b c : RawCell)
    (environment : Env) (field : FieldId) : RawCell :=
  if field != repeated.id then .empty
  else match environment with
    | [(10, 1)] => a
    | [(10, 2)] => b
    | [(10, 3)] => c
    | _ => .empty

def aggregateFilterRead (a b c : RawCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  repeated.checkRaw (aggregateStarRead a b c environment field)

def aggregateComputationFilterRead
    (left right : RowIndex → RawCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  let row := match environment with
    | [(10, current)] => current
    | _ => 0
  if field == filterLeft.id then filterLeft.checkRaw (left row)
  else if field == filterRight.id then filterRight.checkRaw (right row)
  else malformedCheckedCell

def aggregateComputationTargetRead (a b c : RawCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  repeated.checkRaw (aggregateStarRead a b c environment field)

def checkedAggregateErrorOf (authored : SurfaceNumberEntitySource) :
    Option NumberEntityElabError :=
  match elaborateNumberEntitySource model ["Form"] authored with
  | .ok _ => none
  | .error error => some error

def checkedAggregateOf (op : NumericAggregateOp)
    (authored : SurfaceNumberEntitySource) (rows : List RowIndex)
    (a b c : RawCell) (direct : RawFlatContext) : Option NumericOperand :=
  match elaborateNumberEntitySource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateAggregate op (aggregateDocument rows) [] direct
          (aggregateFilterRead a b c) (aggregateStarRead a b c) with
      | .ok result => some result
      | .error _ => none

def checkedValueCountOf (expected : Rat)
    (authored : SurfaceNumberEntitySource) (rows : List RowIndex)
    (a b c : RawCell) (direct : RawFlatContext) : Option NumericOperand :=
  match elaborateNumberEntitySource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateValueCountValidationIn expected
          (aggregateDocument rows) [] (model.checkContext direct)
          (aggregateFilterRead a b c) with
      | .ok result => some result
      | .error _ => none

def aggregateWorld : World :=
  { now := { epochMillis := 0 } }

def checkedAggregateData : DocumentData :=
  { instantiatedRows := [1, 2, 3].map fun row =>
      { group := 10, path := [row] }
    cells := [
      { address := { field := unsignedA.id, path := [] }
        stored := "1", raw := .parsed (.num 1) },
      { address := { field := repeated.id, path := [1] }
        stored := "2", raw := .parsed (.num 2) },
      { address := { field := repeated.id, path := [2] }
        stored := "3", raw := .parsed (.num 3) },
      { address := { field := repeated.id, path := [3] }
        stored := "4", raw := .parsed (.num 4) }] }

inductive CheckedDocumentAggregateSnapshot where
  | result (operand : NumericOperand)
  | error (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

def checkedDocumentAggregateSnapshot (computation : Bool) :
    Option CheckedDocumentAggregateSnapshot := do
  let prepared ←
    (prepareFlatStringContext aggregateWorld builtinStringPatternCompiler
      model).toOption
  let document ← (checkDocument prepared "en_US" checkedAggregateData).toOption
  let source ← (elaborateNumberEntitySource model ["Form"]
    (aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar])).toOption
  pure (match if computation then
      source.evaluateCheckedDocumentComputationAggregate .sum document []
    else
      source.evaluateCheckedDocumentValidationAggregate .sum document [] with
    | .ok operand => .result operand
    | .error cause => .error cause)

def checkedDocumentAggregateStructuralSnapshot
    (computation directFailure : Bool) :
    Option CheckedDocumentAggregateSnapshot := do
  let prepared ←
    (prepareFlatStringContext aggregateWorld builtinStringPatternCompiler
      productModel).toOption
  let data : DocumentData := {
    instantiatedRows := []
    cells := if directFailure then [{
      address := { field := unsignedA.id, path := [] }
      stored := "bad", raw := .rejected .declaredConstraint
    }] else []
  }
  let document ← (checkDocument prepared "en_US" data).toOption
  let source ← (elaborateNumberEntitySource productModel ["Form"]
    (aggregateSource (.field (bare "UnsignedA"))
      [.star (nestedProductStar false)])).toOption
  pure (match if computation then
      source.evaluateCheckedDocumentComputationAggregate .sum document []
    else
      source.evaluateCheckedDocumentValidationAggregate .sum document [] with
    | .ok operand => .result operand
    | .error cause => .error cause)

inductive CheckedDocumentPartialSnapshot where
  | result (result : PartialValidationNumberAggregateResult)
  | error (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

def checkedDocumentPartialStructuralSnapshot
    (directFailure : Bool) :
    Option CheckedDocumentPartialSnapshot := do
  let prepared ←
    (prepareFlatStringContext aggregateWorld builtinStringPatternCompiler
      productModel).toOption
  let data : DocumentData := {
    instantiatedRows := []
    cells := if directFailure then [{
      address := { field := unsignedA.id, path := [] }
      stored := "bad", raw := .rejected .declaredConstraint
    }] else []
  }
  let document ← (checkDocument prepared "en_US" data).toOption
  let source ← (elaborateNumberEntitySource productModel ["Form"]
    (aggregateSource (.field (bare "UnsignedA"))
      [.star (nestedProductStar false)])).toOption
  pure (match source.evaluateCheckedDocumentPartialAggregate
      .sum document [] .full with
    | .ok result => .result result
    | .error cause => .error cause)

def checkedDocumentFilteredAggregateSnapshot
    (computation : Bool) : Option CheckedDocumentAggregateSnapshot := do
  let prepared ←
    (prepareFlatStringContext aggregateWorld builtinStringPatternCompiler
      model).toOption
  let document ← (checkDocument prepared "en_US" checkedAggregateData).toOption
  let source ← (elaborateNumberEntitySource model ["Form"]
    (aggregateSource
      (.starHaving aggregateStar computationAggregateHaving) [])).toOption
  pure (match if computation then
      source.evaluateCheckedDocumentComputationAggregate .sum document []
    else
      source.evaluateCheckedDocumentValidationAggregate .sum document [] with
    | .ok operand => .result operand
    | .error cause => .error cause)

def checkedDocumentValueCountSnapshot
    (computation filtered : Bool) :
    Option CheckedDocumentAggregateSnapshot := do
  let prepared ←
    (prepareFlatStringContext aggregateWorld builtinStringPatternCompiler
      model).toOption
  let document ← (checkDocument prepared "en_US" checkedAggregateData).toOption
  let authored :=
    if filtered then
      aggregateSource
        (.starHaving aggregateStar computationAggregateHaving) []
    else
      aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar]
  let source ← (elaborateNumberEntitySource model ["Form"] authored).toOption
  pure (match if computation then
      source.evaluateCheckedDocumentValueCountComputation 2 document []
    else
      source.evaluateCheckedDocumentValueCountValidation 2 document [] with
    | .ok operand => .result operand
    | .error cause => .error cause)

structure NumberEntityConsumerSlot where
  field : FieldId
  repeated : Bool
  filtered : Bool
  signed : Bool
  deriving Repr, DecidableEq

def numberEntityConsumerSlots
    (source : CheckedNumberEntitySource model) :
    List NumberEntityConsumerSlot :=
  source.operands.map fun
    | .field operand =>
        { field := operand.field.id, repeated := false, filtered := false,
          signed := operand.field.info.signed }
    | .star operand =>
        { field := operand.field.id, repeated := true, filtered := false,
          signed := operand.field.info.signed }
    | .starHaving operand =>
        { field := operand.source.field.id, repeated := true, filtered := true,
          signed := operand.source.field.info.signed }

def checkedDocumentPartialSnapshot
    (valueCount filtered : Bool) (scope : ValidationRelevanceScope) :
    Option (List NumberEntityConsumerSlot × CheckedDocumentPartialSnapshot) := do
  let prepared ←
    (prepareFlatStringContext aggregateWorld builtinStringPatternCompiler
      model).toOption
  let document ← (checkDocument prepared "en_US" checkedAggregateData).toOption
  let authored :=
    if filtered then
      aggregateSource
        (.starHaving aggregateStar computationAggregateHaving) []
    else
      aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar]
  let source ← (elaborateNumberEntitySource model ["Form"] authored).toOption
  let result := match if valueCount then
      source.evaluateCheckedDocumentPartialValueCount 2 document [] scope
    else
      source.evaluateCheckedDocumentPartialAggregate .sum document [] scope with
    | .ok result => .result result
    | .error cause => .error cause
  pure (numberEntityConsumerSlots source, result)

/- Both phases accumulate the same authored direct/star source from one immutable checked document. -/
example :
    checkedDocumentAggregateSnapshot false =
      some (.result (.value 10 .fixed)) ∧
    checkedDocumentAggregateSnapshot true =
      some (.result (.value 10 .fixed)) := by
  native_decide

/- A formal direct prefix hides later missing star scope, while an empty prefix reaches that topology and keeps its failure structural in both phases. -/
example :
    checkedDocumentAggregateStructuralSnapshot false true =
      some (.result (.unknown .declaredConstraint)) ∧
    checkedDocumentAggregateStructuralSnapshot true true =
      some (.result (.unknown .declaredConstraint)) ∧
    checkedDocumentAggregateStructuralSnapshot false false =
      some (.error (.addressing (.missingBinding 10))) ∧
    checkedDocumentAggregateStructuralSnapshot true false =
      some (.error (.addressing (.missingBinding 10))) := by
  native_decide

/- Partial evaluation keeps the same prefix laziness and structural-error boundary rather than mapping a reached addressing failure to UNKNOWN. -/
example :
    checkedDocumentPartialStructuralSnapshot true =
      some (.result (.evaluated (.unknown .declaredConstraint))) ∧
    checkedDocumentPartialStructuralSnapshot false =
      some (.error (.addressing (.missingBinding 10))) := by
  native_decide

/- The checked resolving context feeds both phase-specific filter traversals; empty filter cells compare as zero, so all repeated targets contribute and the reached filter keeps both-directional polarity. -/
example :
    checkedDocumentFilteredAggregateSnapshot false =
      some (.result (.value 9 .both)) ∧
    checkedDocumentFilteredAggregateSnapshot true =
      some (.result (.value 9 .both)) := by
  native_decide

/- Value count reuses the same checked operand route while retaining selected-match provenance for filtered cells. -/
example :
    checkedDocumentValueCountSnapshot false false =
      some (.result (.value 1 .fixed)) ∧
    checkedDocumentValueCountSnapshot true false =
      some (.result (.value 1 .fixed)) ∧
    checkedDocumentValueCountSnapshot false true =
      some (.result (.value 1 .both)) ∧
    checkedDocumentValueCountSnapshot true true =
      some (.result (.value 1 .both)) := by
  native_decide

/- Partial checked-document evaluation preserves concrete direct relevance, wildcard star extent, and rule-level filter skip for both accumulators. -/
example :
    let relevant := ValidationRelevanceScope.partialSet [
      { path := unsignedA.path,
        indices := [.concrete 1, .concrete 1] },
      { path := repeated.path,
        indices := [.concrete 1, .all, .concrete 1] }]
    let unfilteredSlots := [
      { field := unsignedA.id, repeated := false, filtered := false,
        signed := false : NumberEntityConsumerSlot },
      { field := repeated.id, repeated := true, filtered := false,
        signed := false }]
    let filteredSlots := [
      { field := repeated.id, repeated := true, filtered := true,
        signed := false : NumberEntityConsumerSlot }]
    checkedDocumentPartialSnapshot false false relevant =
      some (unfilteredSlots, .result (.evaluated (.value 10 .fixed))) ∧
    checkedDocumentPartialSnapshot true false relevant =
      some (unfilteredSlots, .result (.evaluated (.value 1 .fixed))) ∧
    checkedDocumentPartialSnapshot false false (.partialSet []) =
      some (unfilteredSlots, .result .nonRelevant) ∧
    checkedDocumentPartialSnapshot true false (.partialSet []) =
      some (unfilteredSlots, .result .nonRelevant) ∧
    checkedDocumentPartialSnapshot false true (.partialSet []) =
      some (filteredSlots, .result .skippedHaving) ∧
    checkedDocumentPartialSnapshot true true (.partialSet []) =
      some (filteredSlots, .result .skippedHaving) := by
  native_decide


end A12Kernel.Conformance.NumericAggregateElaboration.CheckedDocument
