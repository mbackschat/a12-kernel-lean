import A12Kernel.Semantics.DateRangeConstruction
import A12Kernel.Semantics.DateRangeOverlapOperators
import A12Kernel.Semantics.HavingEntityList

namespace A12Kernel

/-- Each endpoint keeps its own origin and completion profile; mixed candidate/captured
endpoints are legal in construction equality (spec/05 §8, spec/07 §3). -/
structure HavingDateRangeEndpoint where
  reference : HavingPresenceRef
  format : DateRangeEndpointFormat
  profile : ModelZone.ConcreteProfile
  deriving Repr, DecidableEq

inductive HavingDateRangeOperand where
  | stored (reference : HavingPresenceRef)
  | constructed (start finish : HavingDateRangeEndpoint)
  deriving Repr, DecidableEq

namespace HavingDateRangeOperand

def references : HavingDateRangeOperand → List HavingPresenceRef
  | .stored reference => [reference]
  | .constructed start finish => [start.reference, finish.reference]

def read (source : HavingDateRangeOperand) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error (SimpleComparisonOperand DateRangeCellValue) := do
  let endpoint (source : HavingDateRangeEndpoint) (bound : DateRangeBound) := do
    let cell ← context.read (frame.envAt source.reference.origin) source.reference.field
    source.format.evaluateObservationWith source.profile source.reference.field
      (fun _ => context.unsupportedDateCalendar) (fun _ _ => context.unsupportedDateCalendar)
      bound (observeCell phase cell)
  match source with
  | .stored reference =>
      let cell ← context.read (frame.envAt reference.origin) reference.field
      pure (({ read := fun _ => cell } : FlatContext).resolveDateRangeComparisonOperandAt phase { id := reference.field })
  | .constructed start finish =>
      let start ← endpoint start .start
      let finish ← endpoint finish .finish
      pure (DateRangeConstructionObservation.comparisonOperand { start, finish })

end HavingDateRangeOperand

/-- Construction is confined to equality; overlap retains a scalar role separately from the
ordered entity list, so list-internal pairs cannot decide the scalar operator (spec/05 §8). -/
inductive HavingDateRangePredicate where
  | compare (operator : EqualityOp) (left right : HavingDateRangeOperand)
  | overlap (scalar : Option HavingPresenceRef) (slots : List (HavingFieldListSlot HavingPresenceRef))
  deriving Repr, DecidableEq

namespace HavingDateRangePredicate

def presenceSlots : HavingDateRangePredicate → List (HavingFieldListSlot HavingPresenceRef)
  | .compare _ left right => (left.references ++ right.references).map .direct
  | .overlap scalar slots => scalar.toList.map .direct ++ slots

def references (source : HavingDateRangePredicate) : List HavingPresenceRef :=
  source.presenceSlots.flatMap (·.references)

def readInterval (context : ResolvingCorrelationContext Error) (phase : Phase)
    (environment : Env) (reference : HavingPresenceRef) :
    Except Error (CellObservation (ResolvedDateRange ⊕ YearlessInterval)) := do
  let cell ← context.read environment reference.field
  match observeCell phase cell with
  | .empty => pure .empty
  | .unknown cause | .poison cause =>
      pure (if phase == .validation then .empty else .poison cause)
  | .value (.dateRange (.exact range)) =>
      let some range := range.toResolvedDateRange? | throw context.unsupportedDateCalendar
      pure (.value (.inl range))
  | .value (.dateRange (.yearlessMonth start finish)) =>
      pure (.value (.inr (YearlessInterval.ofMonthPair start finish)))
  | .value (.dateRange (.yearlessMonthDay start finish)) =>
      pure (.value (.inr (YearlessInterval.ofMonthDayPair start finish)))
  | .value _ => throw context.unsupportedDateCalendar

private def overlaps : (ResolvedDateRange ⊕ YearlessInterval) → (ResolvedDateRange ⊕ YearlessInterval) → Bool
  | .inl left, .inl right => left.overlaps right
  | .inr left, .inr right => left.overlaps right
  | _, _ => false

/-- The same continuation-driven entity walk serves direct, fixed-group and starred inputs.
Validation skips formal cells; computation stops at reached poison or a deciding prefix.
The retained 2026-10-08 Having range grid separates these effects and empty-scalar bypass. -/
def evalOverlap (scalar : Option HavingPresenceRef) (slots : List (HavingFieldListSlot HavingPresenceRef))
    (phase : Phase) (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error ComputationConditionResult := do
  let scan (state : ComputationOverlapSearch (ResolvedDateRange ⊕ YearlessInterval)) := do
    match ← HavingFieldListSlot.foldRead (·.origin) (·.field) context frame
        (fun state ref environment => state.step overlaps <$> readInterval context phase environment ref) state slots with
    | .inl _ => pure .notTrue
    | .inr result => pure result
  match scalar with
  | none => scan (.anyPair [])
  | some reference =>
      ComputationOverlapSearch.scalarUsing
        (← readInterval context phase (frame.envAt reference.origin) reference) scan

def evalValidationRead (source : HavingDateRangePredicate)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  match source with
  | .compare operator left right =>
      let left ← left.read .validation context frame
      let right ← right.read .validation context frame
      pure (operator.evalDateRangeCellValues left right)
  | .overlap scalar slots =>
      pure (match ← evalOverlap scalar slots .validation context frame with
        | .holds => .fired .value
        | .notTrue => .notFired
        | .poison _ => .unknown)

def evalComputationRead (source : HavingDateRangePredicate)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error ComputationConditionResult :=
  match source with
  | .compare operator left right => evalComputationComparisonExcept
      (fun a b => operator.holds (a.sameIdentity b))
      (left.read .computation context frame) (fun _ => right.read .computation context frame)
  | .overlap scalar slots => evalOverlap scalar slots .computation context frame

end HavingDateRangePredicate
end A12Kernel
